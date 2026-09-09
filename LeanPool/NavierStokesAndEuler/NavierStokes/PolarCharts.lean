/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.RadialPullback
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Four genuine polar charts with uniform finite-jet bounds

The globally smooth functions constructed below equal the actual local polar
inverse on neighborhoods of four compact sectors. Their global extensions
are not asserted to be a global choice of angle.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.PolarCharts

open Set Filter Function
open scoped ContDiff Topology BigOperators

/-- Plane: an abbreviation for `ℝ × ℝ`. -/
abbrev Plane := ℝ × ℝ
/-- Index: an abbreviation for `Fin 4`. -/
abbrev Index := Fin 4

private theorem nat_le_smooth (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

/-- Rotation by the negative of the chart offset. -/
noncomputable def rotate (j : Index) (p : Plane) : Plane :=
  ![(p.1, p.2), (p.2, -p.1), (-p.1, -p.2), (-p.2, p.1)] j

/-- Unrotate, given by `![(p.1, p.2), (-p.2, p.1), (-p.1, -p.2), (p.2, -p.1)] j`. -/
noncomputable def unrotate (j : Index) (p : Plane) : Plane :=
  ![(p.1, p.2), (-p.2, p.1), (-p.1, -p.2), (p.2, -p.1)] j

/-- Offset, given by `![0, Real.pi / 2, Real.pi, Real.pi + Real.pi / 2] j`. -/
noncomputable def offset (j : Index) : ℝ :=
  ![0, Real.pi / 2, Real.pi, Real.pi + Real.pi / 2] j

theorem rotate_contDiff (j : Index) : ContDiff ℝ ∞ (rotate j) := by
  unfold rotate
  fin_cases j
  · exact (contDiff_id : ContDiff ℝ ∞ (fun p : Plane => p))
  · simpa [rotate] using
      (contDiff_snd.prodMk contDiff_fst.neg : ContDiff ℝ ∞ (fun p : Plane => (p.2, -p.1)))
  · simpa [rotate] using
      (contDiff_fst.neg.prodMk contDiff_snd.neg : ContDiff ℝ ∞ (fun p : Plane => (-p.1, -p.2)))
  · simpa [rotate] using
      (contDiff_snd.neg.prodMk contDiff_fst : ContDiff ℝ ∞ (fun p : Plane => (-p.2, p.1)))

theorem unrotate_rotate (j : Index) (p : Plane) : unrotate j (rotate j p) = p := by
  fin_cases j <;> simp [rotate, unrotate]

theorem rotate_unrotate (j : Index) (p : Plane) : rotate j (unrotate j p) = p := by
  fin_cases j <;> simp [rotate, unrotate]

theorem norm_rotate (j : Index) (p : Plane) : ‖rotate j p‖ = ‖p‖ := by
  fin_cases j <;> simp [rotate, Prod.norm_def, max_comm]

theorem rotate_sum_sq (j : Index) (p : Plane) :
    (rotate j p).1 ^ 2 + (rotate j p).2 ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
  fin_cases j <;> simp [rotate] <;> ring

/-- Radius, given by `Real.sqrt (p.1 ^ 2 + p.2 ^ 2)`. -/
noncomputable def radius (p : Plane) : ℝ := Real.sqrt (p.1 ^ 2 + p.2 ^ 2)

theorem radius_nonneg (p : Plane) : 0 ≤ radius p := Real.sqrt_nonneg _

theorem radius_sq (p : Plane) : radius p ^ 2 = p.1 ^ 2 + p.2 ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem radius_continuous : Continuous radius :=
  ((continuous_fst.pow 2).add (continuous_snd.pow 2)).sqrt

theorem norm_le_radius (p : Plane) : ‖p‖ ≤ radius p := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  apply max_le
  · have h := radius_sq p
    have ha := abs_nonneg p.1
    have hr := radius_nonneg p
    nlinarith [sq_abs p.1, sq_nonneg p.2]
  · have h := radius_sq p
    have ha := abs_nonneg p.2
    have hr := radius_nonneg p
    nlinarith [sq_abs p.2, sq_nonneg p.1]

theorem radius_le_two_norm (p : Plane) : radius p ≤ 2 * ‖p‖ := by
  have hx : |p.1| ≤ ‖p‖ := by
    simpa only [Prod.norm_def, Real.norm_eq_abs] using
      (le_max_left |p.1| |p.2|)
  have hy : |p.2| ≤ ‖p‖ := by
    simpa only [Prod.norm_def, Real.norm_eq_abs] using
      (le_max_right |p.1| |p.2|)
  have hx2 := sq_le_sq₀ (abs_nonneg p.1) (norm_nonneg p) |>.2 hx
  have hy2 := sq_le_sq₀ (abs_nonneg p.2) (norm_nonneg p) |>.2 hy
  have hr := radius_nonneg p
  have hn := norm_nonneg p
  nlinarith [radius_sq p, sq_abs p.1, sq_abs p.2, sq_nonneg ‖p‖]

theorem radius_pos_of_fst_pos {p : Plane} (hp : 0 < p.1) : 0 < radius p := by
  apply Real.sqrt_pos.2
  nlinarith [sq_nonneg p.2]

theorem radius_rotate (j : Index) (p : Plane) : radius (rotate j p) = radius p := by
  simp only [radius, rotate_sum_sq]

/-- The genuine Cartesian map, with radius in the first coordinate. -/
noncomputable def polar (q : Plane) : Plane :=
  (q.1 * Real.cos q.2, q.1 * Real.sin q.2)

theorem polar_contDiff : ContDiff ℝ ∞ polar :=
  (contDiff_fst.mul contDiff_snd.cos).prodMk (contDiff_fst.mul contDiff_snd.sin)

theorem radius_polar (r θ : ℝ) : radius (polar (r, θ)) = |r| := by
  have hs : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  simp only [radius, polar, hs, Real.sqrt_sq_eq_abs]

theorem polar_add_offset (j : Index) (r θ : ℝ) :
    polar (r, θ + offset j) = unrotate j (polar (r, θ)) := by
  fin_cases j <;> ext <;>
    simp [polar, offset, unrotate, Real.cos_add, Real.sin_add]

/-- Base chart, given by `(radius p, Real.arctan (p.2 / p.1))`. -/
noncomputable def baseChart (p : Plane) : Plane :=
  (radius p, Real.arctan (p.2 / p.1))

theorem polar_baseChart {p : Plane} (hp : 0 < p.1) : polar (baseChart p) = p := by
  have hr := radius_pos_of_fst_pos hp
  have hs : Real.sqrt (1 + (p.2 / p.1) ^ 2) = radius p / p.1 := by
    rw [show 1 + (p.2 / p.1) ^ 2 = (p.1 ^ 2 + p.2 ^ 2) / p.1 ^ 2 by
      field_simp]
    rw [Real.sqrt_div (by positivity), Real.sqrt_sq_eq_abs, abs_of_pos hp]
    rfl
  ext <;> simp only [polar, baseChart, Real.cos_arctan, Real.sin_arctan, hs] <;>
    field_simp [hp.ne', hr.ne']

theorem baseChart_polar {r θ : ℝ} (hr : 0 < r)
    (hθ : θ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) : baseChart (polar (r, θ)) = (r, θ) := by
  have he : (r * Real.sin θ) / (r * Real.cos θ) = Real.tan θ := by
    rw [mul_div_mul_left _ _ hr.ne', Real.tan_eq_sin_div_cos]
  ext
  · exact (radius_polar r θ).trans (abs_of_pos hr)
  · simp only [baseChart, polar, he]
    exact Real.arctan_tan hθ.1 hθ.2

/-- A local angle in the interval centered at the fixed chart offset. -/
noncomputable def localChart (j : Index) (p : Plane) : Plane :=
  ((baseChart (rotate j p)).1, (baseChart (rotate j p)).2 + offset j)

theorem localChart_apply (j : Index) (p : Plane) :
    localChart j p = (radius p,
      Real.arctan ((rotate j p).2 / (rotate j p).1) + offset j) := by
  simp only [localChart, baseChart, radius_rotate]

theorem polar_localChart (j : Index) {p : Plane} (hp : 0 < (rotate j p).1) :
    polar (localChart j p) = p := by
  rw [localChart, polar_add_offset, Prod.eta, polar_baseChart hp, unrotate_rotate]

theorem localChart_polar (j : Index) {r θ : ℝ} (hr : 0 < r)
    (hθ : θ - offset j ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    localChart j (polar (r, θ)) = (r, θ) := by
  have hrot : rotate j (polar (r, θ)) = polar (r, θ - offset j) := by
    conv_lhs => arg 2; arg 1; arg 2; rw [show θ = (θ - offset j) + offset j by ring]
    rw [polar_add_offset, rotate_unrotate]
  rw [localChart, hrot, baseChart_polar hr hθ]
  simp

theorem localChart_contDiffAt (j : Index) {p : Plane} (hp : 0 < (rotate j p).1) :
    ContDiffAt ℝ ∞ (localChart j) p := by
  have hc : ContDiffAt ℝ ∞ (rotate j) p := (rotate_contDiff j).contDiffAt
  have hrad : (rotate j p).1 ^ 2 + (rotate j p).2 ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (rotate j p).2]
  exact ((hc.fst.pow 2).add (hc.snd.pow 2)).sqrt hrad |>.prodMk
    ((hc.snd.div hc.fst hp.ne').arctan.add contDiffAt_const)

/-- The original normalized compact annulus uses the product norm. -/
noncomputable def annulus (a b : ℝ) : Set Plane :=
  Metric.closedBall 0 b ∩ {p | a ≤ ‖p‖}

/-- Compact sectors are strictly inside their chart domains. -/
noncomputable def sector (a b : ℝ) (j : Index) : Set Plane :=
  Metric.closedBall 0 b ∩ {p | a / 2 ≤ (rotate j p).1}

/-- Chart domain, given by `{p | a / 4 < (rotate j p).1}`. -/
noncomputable def chartDomain (a : ℝ) (j : Index) : Set Plane :=
  {p | a / 4 < (rotate j p).1}

theorem chartDomain_open (a : ℝ) (j : Index) : IsOpen (chartDomain a j) :=
  isOpen_lt continuous_const (rotate_contDiff j).continuous.fst

theorem sector_isCompact (a b : ℝ) (j : Index) : IsCompact (sector a b j) :=
  (isCompact_closedBall 0 b).inter_right
    (isClosed_le continuous_const (rotate_contDiff j).continuous.fst)

theorem sector_subset_chartDomain {a b : ℝ} (ha : 0 < a) (j : Index) :
    sector a b j ⊆ chartDomain a j := by
  intro p hp
  have hs : a / 2 ≤ (rotate j p).1 := hp.2
  change a / 4 < (rotate j p).1
  linarith

theorem exists_rotate_fst_ge {a : ℝ} {p : Plane} (hp : a ≤ ‖p‖) :
    ∃ j : Index, a ≤ (rotate j p).1 := by
  have hh : a ≤ |p.1| ∨ a ≤ |p.2| := by
    simpa only [Prod.norm_def, Real.norm_eq_abs, le_max_iff] using hp
  rcases hh with hx | hy
  · by_cases hp : 0 ≤ p.1
    · exact ⟨0, by simpa [rotate, abs_of_nonneg hp] using hx⟩
    · exact ⟨2, by simpa [rotate, abs_of_neg (lt_of_not_ge hp)] using hx⟩
  · by_cases hp : 0 ≤ p.2
    · exact ⟨1, by simpa [rotate, abs_of_nonneg hp] using hy⟩
    · exact ⟨3, by simpa [rotate, abs_of_neg (lt_of_not_ge hp)] using hy⟩

theorem annulus_covered {a b : ℝ} (ha : 0 < a) {p : Plane} (hp : p ∈ annulus a b) :
    ∃ j : Index, p ∈ sector a b j := by
  obtain ⟨j, hj⟩ := exists_rotate_fst_ge hp.2
  refine ⟨j, hp.1, ?_⟩
  change a / 2 ≤ (rotate j p).1
  linarith

/-- The same four sectors cover a compact annulus defined by the Euclidean
radius, with the stated margin `rotated x ≥ a/2`. -/
theorem euclidean_annulus_covered {a b : ℝ} {p : Plane}
    (hlo : a ≤ radius p) (hhi : radius p ≤ b) :
    ∃ j : Index, p ∈ sector a b j := by
  have hn : a / 2 ≤ ‖p‖ := by linarith [radius_le_two_norm p]
  obtain ⟨j, hj⟩ := exists_rotate_fst_ge hn
  refine ⟨j, ?_, hj⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (norm_le_radius p).trans hhi

/-- A concrete global extension of the base polar chart. -/
noncomputable def extendedBase (a : ℝ) (p : Plane) : Plane :=
  (Real.sqrt (RadialPullback.positiveRadius (a ^ 2 / 32) (p.1 ^ 2 + p.2 ^ 2)),
    Real.arctan (p.2 / RadialPullback.positiveRadius (a / 8) p.1))

theorem extendedBase_contDiff {a : ℝ} (ha : 0 < a) : ContDiff ℝ ∞ (extendedBase a) := by
  have hr : ContDiff ℝ ∞ (fun p : Plane =>
      RadialPullback.positiveRadius (a ^ 2 / 32) (p.1 ^ 2 + p.2 ^ 2)) :=
    (RadialPullback.positiveRadius_contDiff _).comp ((contDiff_fst.pow 2).add (contDiff_snd.pow 2))
  have hx : ContDiff ℝ ∞ (fun p : Plane => RadialPullback.positiveRadius (a / 8) p.1) :=
    (RadialPullback.positiveRadius_contDiff _).comp contDiff_fst
  exact (hr.sqrt (fun p => (RadialPullback.positiveRadius_pos (by positivity) _).ne')).prodMk
    ((contDiff_snd.div hx (fun p => (RadialPullback.positiveRadius_pos (by
        positivity) _).ne')).arctan)

theorem extendedBase_eq {a : ℝ} (ha : 0 < a) {p : Plane} (hp : a / 4 < p.1) :
    extendedBase a p = baseChart p := by
  have hx : 2 * (a / 8) ≤ p.1 := by linarith
  have hr : 2 * (a ^ 2 / 32) ≤ p.1 ^ 2 + p.2 ^ 2 := by
    have hxp : 0 < p.1 := by linarith
    nlinarith [sq_nonneg p.2, sq_nonneg (p.1 - a / 4)]
  simp only [extendedBase, baseChart, radius,
    RadialPullback.positiveRadius_eq_self (by positivity : 0 < a ^ 2 / 32) hr,
    RadialPullback.positiveRadius_eq_self (by positivity : 0 < a / 8) hx]

/-- Globally smooth chart extension; its polar inverse meaning is local. -/
noncomputable def chart (a : ℝ) (j : Index) (p : Plane) : Plane :=
  ((extendedBase a (rotate j p)).1, (extendedBase a (rotate j p)).2 + offset j)

theorem chart_contDiff {a : ℝ} (ha : 0 < a) (j : Index) : ContDiff ℝ ∞ (chart a j) :=
  (((extendedBase_contDiff ha).comp (rotate_contDiff j)).fst).prodMk
    ((((extendedBase_contDiff ha).comp (rotate_contDiff j)).snd).add contDiff_const)

theorem chart_eq_localChart {a : ℝ} (ha : 0 < a) (j : Index) {p : Plane}
    (hp : p ∈ chartDomain a j) : chart a j p = localChart j p := by
  simp only [chart, extendedBase_eq ha hp, localChart]

theorem chart_eventuallyEq_localChart {a : ℝ} (ha : 0 < a) (j : Index) {p : Plane}
    (hp : p ∈ chartDomain a j) : chart a j =ᶠ[𝓝 p] localChart j := by
  filter_upwards [(chartDomain_open a j).mem_nhds hp] with q hq
  exact chart_eq_localChart ha j hq

theorem polar_chart {a : ℝ} (ha : 0 < a) (j : Index) {p : Plane}
    (hp : p ∈ chartDomain a j) : polar (chart a j p) = p := by
  rw [chart_eq_localChart ha j hp]
  apply polar_localChart
  dsimp [chartDomain] at hp
  linarith

theorem chart_polar {a : ℝ} (ha : 0 < a) (j : Index) {r θ : ℝ}
    (hr : 0 < r) (hθ : θ - offset j ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2))
    (hp : polar (r, θ) ∈ chartDomain a j) : chart a j (polar (r, θ)) = (r, θ) := by
  rw [chart_eq_localChart ha j hp, localChart_polar j hr hθ]

/-- On the compact sectors every actual derivative of the global extension
equals the derivative of the genuine local polar inverse. -/
theorem chart_jet_eq_localChart {a : ℝ} (ha : 0 < a) (j : Index) {p : Plane}
    (hp : p ∈ chartDomain a j) (k : ℕ) :
    iteratedFDeriv ℝ k (chart a j) p = iteratedFDeriv ℝ k (localChart j) p := by
  have he := chart_eventuallyEq_localChart ha j hp
  have he' : chart a j =ᶠ[𝓝[univ] p] localChart j := by simpa using he
  simpa only [iteratedFDerivWithin_univ] using
    he'.iteratedFDerivWithin_eq he.eq_of_nhds k

/-- A single constant bounds all actual jets up to the given order for all
four explicit chart extensions on the fixed closed ball. -/
theorem chart_finiteJets_uniform {a : ℝ} (ha : 0 < a) (b : ℝ) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ j : Index, ∀ k ≤ m, ∀ p ∈ Metric.closedBall (0 : Plane) b,
      ‖iteratedFDeriv ℝ k (chart a j) p‖ ≤ C := by
  have hbound (i : Index × Fin (m + 1)) : ∃ C : ℝ,
      ∀ p ∈ Metric.closedBall (0 : Plane) b,
        ‖iteratedFDeriv ℝ (i.2 : ℕ) (chart a i.1) p‖ ≤ C :=
    (isCompact_closedBall (0 : Plane) b).exists_bound_of_continuousOn
      (((chart_contDiff ha i.1).continuous_iteratedFDeriv (nat_le_smooth i.2)).continuousOn)
  choose B hB using hbound
  refine ⟨1 + ∑ i : Index × Fin (m + 1), |B i|, ?_, ?_⟩
  · have hs : 0 ≤ ∑ i : Index × Fin (m + 1), |B i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    linarith
  · intro j k hk p hp
    let i : Index × Fin (m + 1) := (j, ⟨k, by omega⟩)
    have hs : |B i| ≤ ∑ v : Index × Fin (m + 1), |B v| :=
      Finset.single_le_sum (fun v _ => abs_nonneg (B v)) (Finset.mem_univ i)
    exact (hB i p hp).trans ((le_abs_self (B i)).trans (by linarith))

/-- The compact sectors cover the annulus and carry one uniform bound for the
actual local inverse jets, not merely for a prescribed jet family. -/
theorem localChart_finiteJets_uniform {a : ℝ} (ha : 0 < a) (b : ℝ) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ j : Index, ∀ k ≤ m, ∀ p ∈ sector a b j,
      ‖iteratedFDeriv ℝ k (localChart j) p‖ ≤ C := by
  obtain ⟨C, hC, hB⟩ := chart_finiteJets_uniform ha b m
  refine ⟨C, hC, ?_⟩
  intro j k hk p hp
  rw [← chart_jet_eq_localChart ha j (sector_subset_chartDomain ha j hp) k]
  exact hB j k hk p hp.1

section Scaling

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The exact multilinear chain rule for a linear input change. -/
theorem norm_jet_comp_linear {f : Plane → Plane} (hf : ContDiff ℝ ∞ f)
    (L : E →L[ℝ] Plane) (p : E) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (f ∘ L) p‖ ≤ ‖iteratedFDeriv ℝ k f (L p)‖ * ‖L‖ ^ k := by
  rw [L.iteratedFDeriv_comp_right hf p (nat_le_smooth k)]
  simpa using (iteratedFDeriv ℝ k f (L p)).norm_compContinuousLinearMap_le (fun _ => L)

theorem chart_comp_linear_finiteJets {a : ℝ} (ha : 0 < a) (b : ℝ) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ j : Index, ∀ k ≤ m, ∀ (L : E →L[ℝ] Plane) (p : E),
      L p ∈ Metric.closedBall (0 : Plane) b →
      ‖iteratedFDeriv ℝ k (chart a j ∘ L) p‖ ≤ C * ‖L‖ ^ k := by
  obtain ⟨C, hC, hB⟩ := chart_finiteJets_uniform ha b m
  refine ⟨C, hC, ?_⟩
  intro j k hk L p hp
  exact (norm_jet_comp_linear (chart_contDiff ha j) L p k).trans
    (mul_le_mul_of_nonneg_right (hB j k hk (L p) hp) (pow_nonneg (norm_nonneg _) _))

end Scaling

/-- Scale plane, given by `Q ^ (-(1 / 2 : ℝ)) • ContinuousLinearMap.id ℝ Plane`. -/
noncomputable def scalePlane (Q : ℝ) : Plane →L[ℝ] Plane :=
  Q ^ (-(1 / 2 : ℝ)) • ContinuousLinearMap.id ℝ Plane

@[simp] theorem scalePlane_apply (Q : ℝ) (p : Plane) :
    scalePlane Q p = Q ^ (-(1 / 2 : ℝ)) • p := rfl

theorem norm_scalePlane_le {Q : ℝ} (hQ : 0 < Q) :
    ‖scalePlane Q‖ ≤ Q ^ (-(1 / 2 : ℝ)) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.rpow_nonneg hQ.le _)
  intro p
  rw [scalePlane_apply, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hQ.le _)]

/-- The physical input is scaled by `1 / sqrt Q` before taking the polar chart. -/
noncomputable def physicalChart (a : ℝ) (j : Index) (Q : ℝ) : Plane → Plane :=
  chart a j ∘ scalePlane Q

theorem physicalChart_contDiff {a : ℝ} (ha : 0 < a) (j : Index) (Q : ℝ) :
    ContDiff ℝ ∞ (physicalChart a j Q) :=
  (chart_contDiff ha j).comp (scalePlane Q).contDiff

/-- Each physical derivative costs exactly the fixed half-power of `Q`.
The constant is chosen before `Q`, the chart, and the evaluation point. -/
theorem physicalChart_finiteJets_uniform {a : ℝ} (ha : 0 < a) (b : ℝ) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (Q : ℝ), 0 < Q → ∀ j : Index, ∀ k ≤ m, ∀ p : Plane,
      scalePlane Q p ∈ Metric.closedBall (0 : Plane) b →
      ‖iteratedFDeriv ℝ k (physicalChart a j Q) p‖ ≤ C * Q ^ (-(k : ℝ) / 2) := by
  obtain ⟨C, hC, hB⟩ := chart_comp_linear_finiteJets (E := Plane) ha b m
  refine ⟨C, hC, ?_⟩
  intro Q hQ j k hk p hp
  have h := hB j k hk (scalePlane Q) p hp
  have hs : ‖scalePlane Q‖ ^ k ≤ (Q ^ (-(1 / 2 : ℝ))) ^ k :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_scalePlane_le hQ) k
  have he : (Q ^ (-(1 / 2 : ℝ))) ^ k = Q ^ (-(k : ℝ) / 2) := by
    rw [← Real.rpow_mul_natCast hQ.le]
    congr 1
    ring
  exact h.trans ((mul_le_mul_of_nonneg_left hs (by linarith)).trans_eq (by rw [he]))

theorem rotate_smul (j : Index) (c : ℝ) (p : Plane) : rotate j (c • p) = c • rotate j p := by
  fin_cases j <;> ext <;> simp [rotate, mul_neg]

theorem radius_smul {c : ℝ} (hc : 0 < c) (p : Plane) : radius (c • p) = c * radius p := by
  simp only [radius, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [show (c * p.1) ^ 2 + (c * p.2) ^ 2 = c ^ 2 * (p.1 ^ 2 + p.2 ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs, abs_of_pos hc]

theorem localChart_smul (j : Index) {c : ℝ} (hc : 0 < c) (p : Plane) :
    localChart j (c • p) = (c * (localChart j p).1, (localChart j p).2) := by
  simp only [localChart_apply, radius_smul hc, rotate_smul, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul, mul_div_mul_left _ _ hc.ne']

theorem scalePlane_eq_inv_sqrt {Q : ℝ} (hQ : 0 < Q) (p : Plane) :
    scalePlane Q p = (Real.sqrt Q)⁻¹ • p := by
  rw [scalePlane_apply, Real.rpow_neg hQ.le, Real.sqrt_eq_rpow]

theorem physicalChart_eq {a Q : ℝ} (ha : 0 < a) (hQ : 0 < Q) (j : Index) {p : Plane}
    (hp : scalePlane Q p ∈ chartDomain a j) :
    physicalChart a j Q p = (radius p / Real.sqrt Q, (localChart j p).2) := by
  rw [physicalChart, comp_apply, chart_eq_localChart ha j hp,
    scalePlane_eq_inv_sqrt hQ, localChart_smul j (inv_pos.mpr (Real.sqrt_pos.2 hQ))]
  rw [localChart_apply]
  simp only [inv_mul_eq_div]

theorem physicalChart_inverse {a Q : ℝ} (ha : 0 < a) (hQ : 0 < Q) (j : Index) {p : Plane}
    (hp : scalePlane Q p ∈ chartDomain a j) :
    Real.sqrt Q • polar (physicalChart a j Q p) = p := by
  rw [physicalChart, comp_apply, polar_chart ha j hp, scalePlane_eq_inv_sqrt hQ,
    smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.2 hQ).ne', one_smul]

/-- Angles from two valid local inverse charts differ by an integer full turn. -/
theorem localChart_angle_difference (i j : Index) {p : Plane}
    (hi : 0 < (rotate i p).1) (hj : 0 < (rotate j p).1) :
    ∃ n : ℤ, (localChart i p).2 - (localChart j p).2 = 2 * Real.pi * n := by
  have hr : radius p ≠ 0 := by
    rw [← radius_rotate i p]
    exact (radius_pos_of_fst_pos hi).ne'
  have hxi := congrArg Prod.fst (polar_localChart i hi)
  have hxj := congrArg Prod.fst (polar_localChart j hj)
  have hyi := congrArg Prod.snd (polar_localChart i hi)
  have hyj := congrArg Prod.snd (polar_localChart j hj)
  simp only [polar, localChart_apply] at hxi hxj hyi hyj
  have hcos : Real.cos (localChart i p).2 = Real.cos (localChart j p).2 := by
    apply mul_left_cancel₀ hr
    exact hxi.trans hxj.symm
  have hsin : Real.sin (localChart i p).2 = Real.sin (localChart j p).2 := by
    apply mul_left_cancel₀ hr
    exact hyi.trans hyj.symm
  exact Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp (Real.Angle.cos_sin_inj hcos hsin)

/-- Any function periodic in its angular coordinate has the same chart value.
This applies to integer angular harmonics, not to an unexponentiated phase. -/
theorem localChart_periodic_agree {V : Type*} (f : Plane → V)
    (hf : ∀ r : ℝ, Periodic (fun θ => f (r, θ)) (2 * Real.pi))
    (i j : Index) {p : Plane} (hi : 0 < (rotate i p).1) (hj : 0 < (rotate j p).1) :
    f (localChart i p) = f (localChart j p) := by
  obtain ⟨n, hn⟩ := localChart_angle_difference i j hi hj
  have he : (localChart i p).2 = (localChart j p).2 + n * (2 * Real.pi) := by
    nlinarith [hn]
  have hv := ((hf (radius p)).int_mul n) (localChart j p).2
  have hri : (localChart i p).1 = radius p := by simp only [localChart_apply]
  have hrj : (localChart j p).1 = radius p := by simp only [localChart_apply]
  rw [← Prod.eta (localChart i p), ← Prod.eta (localChart j p), hri, hrj, he]
  exact hv

theorem chart_periodic_agree {V : Type*} {a : ℝ} (ha : 0 < a) (f : Plane → V)
    (hf : ∀ r : ℝ, Periodic (fun θ => f (r, θ)) (2 * Real.pi))
    (i j : Index) {p : Plane} (hi : p ∈ chartDomain a i) (hj : p ∈ chartDomain a j) :
    f (chart a i p) = f (chart a j p) := by
  rw [chart_eq_localChart ha i hi, chart_eq_localChart ha j hj]
  apply localChart_periodic_agree f hf i j
  · have h : a / 4 < (rotate i p).1 := hi
    linarith
  · have h : a / 4 < (rotate j p).1 := hj
    linarith

theorem chart_periodic_eventuallyEq {V : Type*} {a : ℝ} (ha : 0 < a) (f : Plane → V)
    (hf : ∀ r : ℝ, Periodic (fun θ => f (r, θ)) (2 * Real.pi))
    (i j : Index) {p : Plane} (hi : p ∈ chartDomain a i) (hj : p ∈ chartDomain a j) :
    f ∘ chart a i =ᶠ[𝓝 p] f ∘ chart a j := by
  filter_upwards [(chartDomain_open a i).mem_nhds hi, (chartDomain_open a j).mem_nhds hj]
    with q hqi hqj
  exact chart_periodic_agree ha f hf i j hqi hqj

theorem chart_periodic_jets_agree {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a : ℝ} (ha : 0 < a) (f : Plane → V)
    (hf : ∀ r : ℝ, Periodic (fun θ => f (r, θ)) (2 * Real.pi))
    (i j : Index) {p : Plane} (hi : p ∈ chartDomain a i) (hj : p ∈ chartDomain a j) (k : ℕ) :
    iteratedFDeriv ℝ k (f ∘ chart a i) p = iteratedFDeriv ℝ k (f ∘ chart a j) p := by
  have he := chart_periodic_eventuallyEq ha f hf i j hi hj
  have he' : f ∘ chart a i =ᶠ[𝓝[univ] p] f ∘ chart a j := by simpa using he
  simpa only [iteratedFDerivWithin_univ] using
    he'.iteratedFDerivWithin_eq he.eq_of_nhds k

end NavierStokes.PolarCharts
