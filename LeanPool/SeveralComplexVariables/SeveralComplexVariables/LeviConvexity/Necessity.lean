/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.LeviConvexity
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.LeviConvexity.Invariance
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Pseudoconvexity

/-!
# Levi's necessary condition

A domain of holomorphy in any finite-dimensional complex normed space with `C²` boundary is Levi
pseudoconvex. The proof in coordinates is transported by a continuous linear equivalence. This is E.
E. Levi's theorem ([Range][Range1986], Theorem 2.11; [Fritzsche–Grauert][FritzscheGrauert2002],
Theorem 4.7, first half).

The proof avoids holomorphic coordinate changes. If the Levi form of a defining function `ρ`
were negative in a complex tangent direction `w` at a boundary point `p`, the Levi polynomial
provides a quadratic analytic disc `ζ ↦ p + ζ • w + ζ ^ 2 • c + ε • ν` tangent to the boundary
from inside, on which `ρ` behaves like `-ε + ‖ζ‖ ^ 2 L` with `L < 0`. Its boundary circle is
therefore much deeper inside the domain than its center. The boundary distance is comparable to
`|ρ|` near `p`, the center lies in the holomorphic hull of the boundary circle by the maximum
modulus principle, and Thullen's radius bound for domains of holomorphy then forces the center
to be as deep as the circle, a contradiction for small radii.

References: [Range][Range1986] (1986), Chapter II, Theorems 2.9 and 2.11;
[Hörmander][Hormander1973] (1973), Section 2.6; [Fritzsche–Grauert][FritzscheGrauert2002]
(2002), Chapter II, Theorem 4.7.

## Main definitions

* `leviQuadratic`: The complex quadratic coefficient of a real bilinear form along a complex line.

## Main results

* `IsLocalDefiningFunction.exists_disc_estimate`: **Disc estimate along the Levi polynomial.** With
  `c` cancelling the complex quadratic term and `ν` an inward direction, the defining function along
  the disc `ζ ↦ p + ζ • w + ζ ^ 2 • c + (κ r ^ 2) • ν` is `-κ r ^ 2 + ‖ζ‖ ^ 2 L` up to `η r ^ 2`,
  for `‖ζ‖ ≤ r` and `r` small, and the disc lies in any prescribed neighborhood of `p`.
* `IsDomainOfHolomorphy.isLeviPseudoconvex_fin`: **Levi's theorem in coordinates.** A domain of
  holomorphy in `Fin n → ℂ` is Levi pseudoconvex: the Levi form of every local defining function is
  positive semidefinite on the complex tangent space at every boundary point.
* `IsDomainOfHolomorphy.isLeviPseudoconvex`: **Levi's theorem.** A domain of holomorphy in a
  finite-dimensional complex normed space is Levi pseudoconvex: the Levi form of every local
  defining function is positive semidefinite on the complex tangent space at every boundary point.

## References

* [K. Fritzsche and H. Grauert, *From Holomorphic Functions to Complex
  Manifolds*][FritzscheGrauert2002]
* [L. Hörmander, *An Introduction to Complex Analysis in Several Variables*][Hormander1973]
* [R. M. Range, *Holomorphic Functions and Integral Representations in Several Complex
  Variables*][Range1986]
-/

public noncomputable section

open Complex Filter Metric Set
open scoped Topology

namespace SeveralComplexVariables

open TaylorBounds

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable {U : Set E} {p : E} {ρ : E → ℝ} {V : Set E}

/-- An inward direction for a defining function: the real derivative equals `1`. -/
theorem IsLocalDefiningFunction.exists_inward_direction (h : IsLocalDefiningFunction U p ρ V) :
    ∃ ν : E, fderiv ℝ ρ p ν = 1 ∧ 0 < ‖ν‖ :=
  ContinuousLinearMap.exists_apply_eq_one_of_ne_zero h.fderiv_ne

/-- A neighborhood of `p` on which the derivative is Lipschitz-bounded and still points inward. -/
theorem IsLocalDefiningFunction.exists_ball_fderiv_bound_and_inward
    (h : IsLocalDefiningFunction U p ρ V) {ν : E} (hν : fderiv ℝ ρ p ν = 1) :
    ∃ Lip δ₀ : ℝ, 0 < Lip ∧ 0 < δ₀ ∧ ball p δ₀ ⊆
      {y | y ∈ V ∧ ‖fderiv ℝ ρ y‖ ≤ Lip ∧ (1 / 2 : ℝ) ≤ fderiv ℝ ρ y ν} := by
  set ℓ := fderiv ℝ ρ p
  set Lip := ‖ℓ‖ + 1
  have hLip0 : 0 < Lip := by positivity
  have hDcont : ContinuousOn (fderiv ℝ ρ) V :=
    h.contDiffOn.continuousOn_fderiv_of_isOpen h.isOpen (by norm_num)
  have hcontp : ContinuousAt (fderiv ℝ ρ) p := hDcont.continuousAt (h.isOpen.mem_nhds h.mem)
  have hev : ∀ᶠ y in 𝓝 p, y ∈ V ∧ ‖fderiv ℝ ρ y‖ ≤ Lip ∧ (1 / 2 : ℝ) ≤ fderiv ℝ ρ y ν := by
    have h1 : ∀ᶠ y in 𝓝 p, y ∈ V := h.isOpen.mem_nhds h.mem
    have h2 : ∀ᶠ y in 𝓝 p, ‖fderiv ℝ ρ y‖ ≤ Lip :=
      (continuous_norm.continuousAt.comp hcontp).eventually
        (eventually_le_nhds (show ‖fderiv ℝ ρ p‖ < Lip by linarith))
    have h3 : ∀ᶠ y in 𝓝 p, (1 / 2 : ℝ) ≤ fderiv ℝ ρ y ν := by
      have hc : ContinuousAt (fun y => fderiv ℝ ρ y ν) p :=
        (ContinuousLinearMap.apply ℝ ℝ ν).continuous.continuousAt.comp hcontp
      exact hc.eventually (eventually_ge_nhds (show (1 / 2 : ℝ) < fderiv ℝ ρ p ν by
        rw [hν]; norm_num))
    exact h1.and (h2.and h3) |>.mono fun y hy => ⟨hy.1, hy.2.1, hy.2.2⟩
  obtain ⟨δ₀, hδ₀, hball₀⟩ := Metric.mem_nhds_iff.mp hev
  exact ⟨Lip, δ₀, hLip0, hδ₀, hball₀⟩

/-- Lower bound: distance to the complement is at least a multiple of `|ρ|`. -/
theorem IsLocalDefiningFunction.mul_abs_le_infDist (hU : IsOpen U) (hp : p ∈ frontier U)
    (h : IsLocalDefiningFunction U p ρ V) {Lip δ₀ : ℝ} (hLip0 : 0 < Lip) (hδ₀ : 0 < δ₀)
    (hball₀ : ball p δ₀ ⊆ {y | y ∈ V ∧ ‖fderiv ℝ ρ y‖ ≤ Lip})
    {z : E} (hz : z ∈ ball p (δ₀ / 2)) (hzU : z ∈ U)
    (hρsmall : |ρ z| < Lip * δ₀ / 2) : |ρ z| / Lip ≤ infDist z Uᶜ := by
  have hUc : Uᶜ.Nonempty := ⟨p, hU.notMem_of_mem_frontier hp⟩
  have hdiff : ∀ y ∈ V, DifferentiableAt ℝ ρ y := fun y hy =>
    (h.contDiffOn.contDiffAt (h.isOpen.mem_nhds hy)).differentiableAt (by norm_num)
  have hρz : ρ z < 0 := h.neg_of_mem (hball₀ (ball_subset_ball (half_le_self hδ₀.le) hz)).1 hzU
  have hρabs : |ρ z| = -ρ z := abs_of_neg hρz
  rw [le_infDist hUc]
  intro y hy
  by_cases hyV : y ∈ ball p δ₀
  · have hρy : 0 ≤ ρ y := by
      by_contra hneg
      push Not at hneg
      exact hy (h.mem_of_neg (hball₀ hyV).1 hneg)
    have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (f := ρ) (s := ball p δ₀) (C := Lip)
      (fun x hx => hdiff x (hball₀ hx).1) (fun x hx => (hball₀ hx).2) (convex_ball p δ₀)
      (ball_subset_ball (half_le_self hδ₀.le) hz) hyV
    rw [Real.norm_eq_abs, ← dist_eq_norm, dist_comm] at hmv
    have : |ρ z| ≤ |ρ y - ρ z| := by
      rw [hρabs, abs_of_nonneg (by linarith)]
      linarith
    rw [div_le_iff₀ hLip0]
    linarith
  · have hdz : δ₀ / 2 ≤ dist z y := by
      have h1 : δ₀ ≤ dist y p := not_lt.mp (by simpa [mem_ball] using hyV)
      have h2 : dist z p < δ₀ / 2 := mem_ball.mp hz
      have := dist_triangle y z p
      rw [dist_comm y z] at this
      linarith
    have : |ρ z| / Lip ≤ δ₀ / 2 := by
      rw [div_le_iff₀ hLip0]
      linarith
    exact this.trans hdz

/-- Upper bound: walking inward along `ν` reaches the complement at distance `O(|ρ|)`. -/
theorem IsLocalDefiningFunction.infDist_le_mul_abs (h : IsLocalDefiningFunction U p ρ V)
    {ν : E} {Lip δ₀ : ℝ} (hδ₀ : 0 < δ₀) (hν0 : 0 < ‖ν‖)
    (hball₀ : ball p δ₀ ⊆
      {y | y ∈ V ∧ ‖fderiv ℝ ρ y‖ ≤ Lip ∧ (1 / 2 : ℝ) ≤ fderiv ℝ ρ y ν})
    {z : E} (hz : z ∈ ball p (δ₀ / 2)) (hzU : z ∈ U)
    (hρsmall : |ρ z| < δ₀ / (4 * ‖ν‖)) : infDist z Uᶜ ≤ 2 * ‖ν‖ * |ρ z| := by
  have hdiff : ∀ y ∈ V, DifferentiableAt ℝ ρ y := fun y hy =>
    (h.contDiffOn.contDiffAt (h.isOpen.mem_nhds hy)).differentiableAt (by norm_num)
  have hzV : z ∈ V := (hball₀ (ball_subset_ball (half_le_self hδ₀.le) hz)).1
  have hρz : ρ z < 0 := h.neg_of_mem hzV hzU
  have hρabs : |ρ z| = -ρ z := abs_of_neg hρz
  set T : ℝ := 2 * |ρ z|
  have hT0 : 0 ≤ T := by positivity
  have hseg : ∀ t ∈ Icc (0 : ℝ) T, z + t • ν ∈ ball p δ₀ := by
    intro t ht
    have h1 : ‖t • ν‖ ≤ T * ‖ν‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
    have h2 : T * ‖ν‖ < δ₀ / 2 := by
      rw [lt_div_iff₀ (by positivity)] at hρsmall
      nlinarith
    rw [mem_ball, dist_eq_norm]
    calc ‖z + t • ν - p‖ ≤ ‖z - p‖ + ‖t • ν‖ := by
          rw [add_sub_right_comm]; exact norm_add_le _ _
      _ < δ₀ / 2 + δ₀ / 2 := by
          have := mem_ball.mp hz
          rw [dist_eq_norm] at this
          linarith
      _ = δ₀ := by ring
  have hderiv : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt (fun t : ℝ => ρ (z + t • ν))
      (fderiv ℝ ρ (z + t • ν) ν) t := by
    intro t ht
    have hl : HasDerivAt (fun t : ℝ => z + t • ν) ν t := by
      simpa using ((hasDerivAt_id t).smul_const ν).const_add z
    exact (hdiff _ (hball₀ (hseg t ht)).1).hasFDerivAt.comp_hasDerivAt t hl
  have hmono := Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc 0 T)
    (f := fun t : ℝ => ρ (z + t • ν)) (C := 1 / 2)
    (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    (fun t ht => by
      rw [(hderiv t (interior_subset ht)).deriv]
      exact (hball₀ (hseg t (interior_subset ht))).2.2)
    0 (left_mem_Icc.mpr hT0) T (right_mem_Icc.mpr hT0) hT0
  simp only [zero_smul, add_zero, sub_zero] at hmono
  have hρT : 0 ≤ ρ (z + T • ν) := by
    dsimp [T] at hmono ⊢
    rw [hρabs] at hmono ⊢
    linarith
  have hnot : z + T • ν ∉ U := fun hmem =>
    absurd (h.neg_of_mem (hball₀ (hseg T (right_mem_Icc.mpr hT0))).1 hmem) (not_lt.mpr hρT)
  calc infDist z Uᶜ ≤ dist z (z + T • ν) := infDist_le_dist_of_mem hnot
    _ = T * ‖ν‖ := by
        rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg hT0]
    _ = 2 * ‖ν‖ * |ρ z| := by dsimp [T]; ring

/-- Near a boundary point, a defining function is comparable to the distance to the complement: `c₂
* |ρ z| ≤ infDist z Uᶜ ≤ C₁ * |ρ z|` for `z ∈ U` near `p`. -/
theorem IsLocalDefiningFunction.exists_infDist_bounds (hU : IsOpen U) (hp : p ∈ frontier U)
    (h : IsLocalDefiningFunction U p ρ V) :
    ∃ C₁ c₂ δ : ℝ, 0 < C₁ ∧ 0 < c₂ ∧ 0 < δ ∧ ∀ z ∈ ball p δ, z ∈ U →
      c₂ * |ρ z| ≤ infDist z Uᶜ ∧ infDist z Uᶜ ≤ C₁ * |ρ z| := by
  obtain ⟨ν, hℓν, hν0⟩ := h.exists_inward_direction
  obtain ⟨Lip, δ₀, hLip0, hδ₀, hball₀⟩ := h.exists_ball_fderiv_bound_and_inward hℓν
  have hdiff : ∀ y ∈ V, DifferentiableAt ℝ ρ y := fun y hy =>
    (h.contDiffOn.contDiffAt (h.isOpen.mem_nhds hy)).differentiableAt (by norm_num)
  have hρcont : ContinuousAt ρ p := (hdiff p h.mem).continuousAt
  have hsmall : ∀ᶠ z in 𝓝 p, |ρ z| < min (Lip * δ₀ / 2) (δ₀ / (4 * ‖ν‖)) := by
    have hcabs : ContinuousAt (fun z => |ρ z|) p := hρcont.abs
    exact hcabs.eventually (eventually_lt_nhds (show |ρ p| < min (Lip * δ₀ / 2) (δ₀ / (4 * ‖ν‖)) by
      rw [h.eq_zero, abs_zero]; exact lt_min (by positivity) (by positivity)))
  obtain ⟨δ₁, hδ₁, hball₁⟩ := Metric.mem_nhds_iff.mp hsmall
  refine ⟨2 * ‖ν‖, 1 / Lip, min (δ₀ / 2) δ₁, by positivity, by positivity, by positivity, ?_⟩
  intro z hz hzU
  have hzδ₀ : z ∈ ball p (δ₀ / 2) := ball_subset_ball (min_le_left _ _) hz
  have hρsmall : |ρ z| < min (Lip * δ₀ / 2) (δ₀ / (4 * ‖ν‖)) :=
    hball₁ (ball_subset_ball (min_le_right _ _) hz)
  refine ⟨?_, ?_⟩
  · rw [div_mul_eq_mul_div, one_mul]
    exact h.mul_abs_le_infDist hU hp hLip0 hδ₀
      (fun y hy => ⟨(hball₀ hy).1, (hball₀ hy).2.1⟩) hzδ₀ hzU (lt_min_iff.mp hρsmall).1
  · exact h.infDist_le_mul_abs hδ₀ hν0 hball₀ hzδ₀ hzU (lt_min_iff.mp hρsmall).2

/-- The complex quadratic coefficient of a real bilinear form along a complex line. -/
@[expose] def leviQuadratic (B : E →L[ℝ] E →L[ℝ] ℝ) (w : E) : ℂ :=
  (((B w w - B (I • w) (I • w)) / 4 : ℝ) : ℂ) - I / 2 * (B w (I • w) : ℝ)

/-- **Disc estimate along the Levi polynomial.** With `c` cancelling the complex quadratic
term and `ν` an inward direction, the defining function along the disc
`ζ ↦ p + ζ • w + ζ ^ 2 • c + (κ r ^ 2) • ν` is `-κ r ^ 2 + ‖ζ‖ ^ 2 L` up to `η r ^ 2`, for
`‖ζ‖ ≤ r` and `r` small, and the disc lies in any prescribed neighborhood of `p`. -/
theorem IsLocalDefiningFunction.exists_disc_estimate (h : IsLocalDefiningFunction U p ρ V)
    {w : E} (hw : IsComplexTangent ρ p w) {c ν : E}
    (hc : complexPart (fderiv ℝ ρ p) c = -leviQuadratic (fderiv ℝ (fderiv ℝ ρ) p) w)
    (hν : fderiv ℝ ρ p ν = -1) {κ η : ℝ} (hκ : 0 ≤ κ) (hη : 0 < η) {W : Set E} (hW : W ∈ 𝓝 p) :
    ∃ r₀ > 0, ∀ r, 0 < r → r ≤ r₀ → ∀ ζ : ℂ, ‖ζ‖ ≤ r →
      p + ζ • w + ζ ^ 2 • c + (κ * r ^ 2) • ν ∈ W ∧
      |ρ (p + ζ • w + ζ ^ 2 • c + (κ * r ^ 2) • ν) - (-(κ * r ^ 2) + ‖ζ‖ ^ 2 * leviForm ρ p w)|
        ≤ η * r ^ 2 := by
  set ℓ := fderiv ℝ ρ p with hℓ
  set B := fderiv ℝ (fderiv ℝ ρ) p with hB
  have hρp : ContDiffAt ℝ 2 ρ p := h.contDiffOn.contDiffAt (h.isOpen.mem_nhds h.mem)
  -- symmetry of the second derivative
  have hev : ∀ᶠ y in 𝓝 p, HasFDerivAt ρ (fderiv ℝ ρ y) y := by
    filter_upwards [h.isOpen.mem_nhds h.mem] with y hy
    exact ((h.contDiffOn.contDiffAt (h.isOpen.mem_nhds hy)).differentiableAt (by
      norm_num)).hasFDerivAt
  have hBd : HasFDerivAt (fderiv ℝ ρ) B p :=
    ((hρp.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hsymm : ∀ v v', B v v' = B v' v := second_derivative_symmetric_of_eventually hev hBd
  -- constants
  set M₀ : ℝ := ‖w‖ + ‖c‖ + κ * ‖ν‖ with hM₀
  have hM₀0 : 0 ≤ M₀ := by positivity
  set M₁ : ℝ := ‖B‖ * ‖w‖ * (‖c‖ + κ * ‖ν‖) + ‖B‖ * (‖c‖ + κ * ‖ν‖) ^ 2 / 2 with hM₁
  have hM₁0 : 0 ≤ M₁ := by positivity
  obtain ⟨δ', hδ', htaylor⟩ := exists_taylor_bound hρp (ε := η / (2 * (M₀ ^ 2 + 1))) (by positivity)
  obtain ⟨δW, hδW, hballW⟩ := Metric.mem_nhds_iff.mp hW
  set δt := min δ' δW
  have hδt : 0 < δt := lt_min hδ' hδW
  refine ⟨min 1 (min (η / (2 * (M₁ + 1))) (δt / (2 * (M₀ + 1)))), by positivity,
    fun r hr hr₀ ζ hζ => ?_⟩
  obtain ⟨hr1, hrM₁, hrδt⟩ := le_one_and_mul_add_le_of_le_min hM₀0 hM₁0 hr hr₀
  have hrδ' : r * (M₀ + 1) < δ' := hrδt.trans_le (min_le_left _ _)
  have hrδW : r * (M₀ + 1) < δW := hrδt.trans_le (min_le_right _ _)
  -- the increment and its pieces
  set h₁ : E := ζ • w with hh₁
  set h₂ : E := ζ ^ 2 • c + (κ * r ^ 2) • ν with hh₂
  have hsplit : p + ζ • w + ζ ^ 2 • c + (κ * r ^ 2) • ν = p + (h₁ + h₂) := by
    rw [hh₁, hh₂]; abel
  have hζr2 : ‖ζ‖ ^ 2 ≤ r ^ 2 := by gcongr
  have hn₁ : ‖h₁‖ ≤ r * ‖w‖ := by
    rw [hh₁, norm_smul]
    exact mul_le_mul_of_nonneg_right hζ (norm_nonneg _)
  have hn₂ : ‖h₂‖ ≤ r ^ 2 * (‖c‖ + κ * ‖ν‖) := by
    rw [hh₂]
    calc ‖ζ ^ 2 • c + (κ * r ^ 2) • ν‖ ≤ ‖ζ ^ 2 • c‖ + ‖(κ * r ^ 2) • ν‖ := norm_add_le _ _
      _ = ‖ζ‖ ^ 2 * ‖c‖ + κ * r ^ 2 * ‖ν‖ := by
          rw [norm_smul, norm_smul, norm_pow, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      _ ≤ r ^ 2 * ‖c‖ + κ * r ^ 2 * ‖ν‖ := by gcongr
      _ = r ^ 2 * (‖c‖ + κ * ‖ν‖) := by ring
  have hn₂' : ‖h₂‖ ≤ r * (‖c‖ + κ * ‖ν‖) := by
    refine hn₂.trans ?_
    have : r ^ 2 ≤ r := by nlinarith
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have hn : ‖h₁ + h₂‖ ≤ r * M₀ := by
    calc ‖h₁ + h₂‖ ≤ ‖h₁‖ + ‖h₂‖ := norm_add_le _ _
      _ ≤ r * ‖w‖ + r * (‖c‖ + κ * ‖ν‖) := add_le_add hn₁ hn₂'
      _ = r * M₀ := by rw [hM₀]; ring
  have hnlt : ‖h₁ + h₂‖ < δ' := hn.trans_lt (by nlinarith)
  constructor
  · rw [hsplit]
    apply hballW
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact hn.trans_lt (by nlinarith)
  -- the Taylor expansion
  have ht := htaylor (h₁ + h₂) hnlt
  -- linear term
  have hℓw : complexPart ℓ w = 0 := by
    have h1 : ℓ w = 0 := hw.1
    have h2 : ℓ (I • w) = 0 := hw.2
    simp [complexPart_apply, h1, h2]
  have hlin : ℓ (h₁ + h₂) = (ζ ^ 2 * (-leviQuadratic B w)).re - κ * r ^ 2 := by
    rw [hh₁, hh₂, map_add, map_add, apply_smul_eq_re_mul_complexPart ℓ ζ w,
      apply_smul_eq_re_mul_complexPart ℓ (ζ ^ 2) c, hℓw, hc, map_smul, smul_eq_mul, hν]
    simp
    ring
  -- quadratic term
  have hquad : (1 / 2 : ℝ) * B (h₁ + h₂) (h₁ + h₂) =
      (1 / 2 : ℝ) * B h₁ h₁ + B h₁ h₂ + (1 / 2 : ℝ) * B h₂ h₂ := by
    simp only [map_add, add_apply, hsymm h₂ h₁]
    ring
  have hquad₁ : (1 / 2 : ℝ) * B h₁ h₁ = ‖ζ‖ ^ 2 * leviForm ρ p w + (ζ ^ 2 * leviQuadratic B w).re
    := by
    rw [hh₁, bilinear_smul_smul_eq B (hsymm w (I • w)) ζ, leviForm_eq_fderiv, leviQuadratic]
  -- cancellation of the complex quadratic terms
  have hcancel : (ζ ^ 2 * (-leviQuadratic B w)).re + (ζ ^ 2 * leviQuadratic B w).re = 0 := by
    rw [mul_neg, Complex.neg_re]; ring
  -- error bounds
  have hBn : 0 ≤ ‖B‖ := ContinuousLinearMap.opNorm_nonneg B
  have hB₁₂ : |B h₁ h₂| ≤ ‖B‖ * ‖w‖ * (‖c‖ + κ * ‖ν‖) * r ^ 3 := by
    have := B.le_opNorm₂ h₁ h₂
    rw [Real.norm_eq_abs] at this
    refine this.trans ?_
    calc ‖B‖ * ‖h₁‖ * ‖h₂‖ ≤ ‖B‖ * (r * ‖w‖) * (r ^ 2 * (‖c‖ + κ * ‖ν‖)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hn₁ hBn) hn₂ (norm_nonneg _) (by positivity)
      _ = ‖B‖ * ‖w‖ * (‖c‖ + κ * ‖ν‖) * r ^ 3 := by ring
  have hB₂₂ : |(1 / 2 : ℝ) * B h₂ h₂| ≤ ‖B‖ * (‖c‖ + κ * ‖ν‖) ^ 2 / 2 * r ^ 3 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    have := B.le_opNorm₂ h₂ h₂
    rw [Real.norm_eq_abs] at this
    have h2 : ‖B‖ * ‖h₂‖ * ‖h₂‖ ≤ ‖B‖ * (r * (‖c‖ + κ * ‖ν‖)) * (r ^ 2 * (‖c‖ + κ * ‖ν‖)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hn₂' hBn) hn₂ (norm_nonneg _) (by positivity)
    calc 1 / 2 * |B h₂ h₂| ≤ 1 / 2 * (‖B‖ * (r * (‖c‖ + κ * ‖ν‖)) * (r ^ 2 * (‖c‖ + κ * ‖ν‖))) :=
          mul_le_mul_of_nonneg_left (this.trans h2) (by norm_num)
      _ = ‖B‖ * (‖c‖ + κ * ‖ν‖) ^ 2 / 2 * r ^ 3 := by ring
  have hR : |ρ (p + (h₁ + h₂)) - ρ p - ℓ (h₁ + h₂) - (1 / 2 : ℝ) * B (h₁ + h₂) (h₁ + h₂)|
      ≤ η / (2 * (M₀ ^ 2 + 1)) * (r * M₀) ^ 2 :=
    ht.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn 2) (by positivity))
  have hcub : |B h₁ h₂ + (1 / 2 : ℝ) * B h₂ h₂| ≤ M₁ * r ^ 3 :=
    (abs_add_le _ _).trans (by rw [hM₁, add_mul]; exact add_le_add hB₁₂ hB₂₂)
  rw [hsplit]
  have hkey : ρ (p + (h₁ + h₂)) - (-(κ * r ^ 2) + ‖ζ‖ ^ 2 * leviForm ρ p w) =
      (ρ (p + (h₁ + h₂)) - ρ p - ℓ (h₁ + h₂) - (1 / 2 : ℝ) * B (h₁ + h₂) (h₁ + h₂)) +
        (B h₁ h₂ + (1 / 2 : ℝ) * B h₂ h₂) := by
    rw [h.eq_zero, hlin, hquad, hquad₁]
    linarith [hcancel]
  rw [hkey]
  exact taylor_remainder_add_cubic_le hr hη hrM₁ hR hcub

variable {n : ℕ}

/-- The Levi polynomial disc of small radius lies in `U` when the Levi form is negative. -/
theorem IsLocalDefiningFunction.disc_subset_of_estimate {U : Set (Fin n → ℂ)}
    {p : Fin n → ℂ} {ρ : (Fin n → ℂ) → ℝ} {V : Set (Fin n → ℂ)}
    (h : IsLocalDefiningFunction U p ρ V) {φ : ℂ → Fin n → ℂ} {r κ η L : ℝ}
    (hr : 0 < r) (hκ : 0 < κ) (hL : L < 0) (hηκ : η ≤ κ / 2)
    (hest : ∀ ζ, ‖ζ‖ ≤ r → φ ζ ∈ V ∧
      |ρ (φ ζ) - (-(κ * r ^ 2) + ‖ζ‖ ^ 2 * L)| ≤ η * r ^ 2) :
    ∀ ζ ∈ closedBall (0 : ℂ) r, φ ζ ∈ U := by
  intro ζ hζ
  obtain ⟨hmem, hρ⟩ := hest ζ (mem_closedBall_zero_iff.mp hζ)
  apply h.mem_of_neg hmem
  have h1 := (abs_le.mp hρ).2
  have h2 : ‖ζ‖ ^ 2 * L ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hL.le
  have h3 : η * r ^ 2 ≤ κ / 2 * r ^ 2 := mul_le_mul_of_nonneg_right hηκ (by positivity)
  have h4 : 0 < κ / 2 * r ^ 2 := by positivity
  linarith

/-- **Levi's theorem in coordinates.** A domain of holomorphy in `Fin n → ℂ` is Levi
pseudoconvex: the Levi form of every local defining function is positive semidefinite on the
complex tangent space at every boundary point. The coordinate-free version is
`IsDomainOfHolomorphy.isLeviPseudoconvex`. -/
theorem IsDomainOfHolomorphy.isLeviPseudoconvex_fin {U : Set (Fin n → ℂ)}
    (hU : IsDomainOfHolomorphy U) (ho : IsOpen U) : IsLeviPseudoconvex U := by
  intro p hp ρ V h w hw
  by_contra hneg
  push Not at hneg
  set L := leviForm ρ p w
  set ℓ := fderiv ℝ ρ p
  set B := fderiv ℝ (fderiv ℝ ρ) p
  obtain ⟨c, hc⟩ := exists_complexPart_eq h.fderiv_ne (-leviQuadratic B w)
  obtain ⟨ν0, hν0, _⟩ := ContinuousLinearMap.exists_apply_eq_one_of_ne_zero h.fderiv_ne
  set ν : Fin n → ℂ := -ν0
  have hℓν : ℓ ν = -1 := by rw [map_neg, hν0]
  obtain ⟨C₁, c₂, δ, hC₁, hc₂, hδ, hdist⟩ := h.exists_infDist_bounds ho hp
  set κ : ℝ := c₂ * (-L) / (8 * C₁) with hκ
  have hκ0 : 0 < κ := by
    rw [hκ]
    have : 0 < -L := by linarith
    positivity
  set η : ℝ := min (κ / 2) (-L / 2) with hη
  have hη0 : 0 < η := lt_min (by positivity) (by linarith)
  have hηκ : η ≤ κ / 2 := min_le_left _ _
  have hηL : η ≤ -L / 2 := min_le_right _ _
  obtain ⟨r, hr, hest⟩ := h.exists_disc_estimate hw hc hℓν hκ0.le hη0
    (W := V ∩ ball p δ) (inter_mem (h.isOpen.mem_nhds h.mem) (ball_mem_nhds p hδ))
  set φ : ℂ → Fin n → ℂ := fun ζ => p + ζ • w + ζ ^ 2 • c + (κ * r ^ 2) • ν with hφ
  have hφan : AnalyticOnNhd ℂ φ (closedBall 0 r) := fun ζ _ =>
    ((analyticAt_const.add (analyticAt_id.smul analyticAt_const)).add
      ((analyticAt_id.pow 2).smul analyticAt_const)).add analyticAt_const
  have hest' : ∀ ζ : ℂ, ‖ζ‖ ≤ r → φ ζ ∈ V ∩ ball p δ ∧
      |ρ (φ ζ) - (-(κ * r ^ 2) + ‖ζ‖ ^ 2 * L)| ≤ η * r ^ 2 := hest r hr le_rfl
  have hdiscU : ∀ ζ ∈ closedBall (0 : ℂ) r, φ ζ ∈ U :=
    h.disc_subset_of_estimate hr hκ0 hneg hηκ fun ζ hζ =>
      ⟨(hest' ζ hζ).1.1, (hest' ζ hζ).2⟩
  -- the boundary circle is deep inside
  set m : ℝ := c₂ * (-L) / 2 * r ^ 2 with hm
  have hm0 : 0 < m := by
    have : 0 < -L := by linarith
    positivity
  have hcircle : ∀ ζ ∈ sphere (0 : ℂ) r, m ≤ infDist (φ ζ) Uᶜ := by
    intro ζ hζ
    have hζ' : ‖ζ‖ = r := mem_sphere_zero_iff_norm.mp hζ
    obtain ⟨hmem, hρ⟩ := hest' ζ hζ'.le
    have hin := hdiscU ζ (sphere_subset_closedBall hζ)
    have hlow := (hdist (φ ζ) hmem.2 hin).1
    have h1 := (abs_le.mp hρ).2
    rw [hζ'] at h1
    have hρneg : ρ (φ ζ) ≤ L / 2 * r ^ 2 := by
      have h3 : η * r ^ 2 ≤ -L / 2 * r ^ 2 := mul_le_mul_of_nonneg_right hηL (by positivity)
      have h4 : 0 ≤ κ * r ^ 2 := by positivity
      linarith
    have habs : -L / 2 * r ^ 2 ≤ |ρ (φ ζ)| := by
      rw [abs_of_nonpos (by nlinarith [pow_pos hr 2])]
      linarith
    calc m = c₂ * (-L / 2 * r ^ 2) := by rw [hm]; ring
      _ ≤ c₂ * |ρ (φ ζ)| := mul_le_mul_of_nonneg_left habs hc₂.le
      _ ≤ infDist (φ ζ) Uᶜ := hlow
  -- the center is shallow
  have hcenter : infDist (φ 0) Uᶜ ≤ C₁ * (2 * κ * r ^ 2) := by
    obtain ⟨hmem, hρ⟩ := hest' 0 (by simp [hr.le])
    have hin := hdiscU 0 (mem_closedBall_self hr.le)
    have hup := (hdist (φ 0) hmem.2 hin).2
    have habs : |ρ (φ 0)| ≤ 2 * κ * r ^ 2 := by
      have h0 : ‖(0 : ℂ)‖ ^ 2 * L = 0 := by simp
      rw [h0, add_zero, sub_neg_eq_add] at hρ
      have h3 : η * r ^ 2 ≤ κ / 2 * r ^ 2 := mul_le_mul_of_nonneg_right hηκ (by positivity)
      have hκr : 0 ≤ κ * r ^ 2 := by positivity
      have := abs_le.mp hρ
      rw [abs_le]
      constructor <;> linarith
    exact hup.trans (mul_le_mul_of_nonneg_left habs hC₁.le)
  -- Thullen's radius bound
  have hhull := mem_holomorphicHull_of_analytic_disc hr hφan hdiscU (mem_closedBall_self hr.le)
  have hK : IsCompact (φ '' sphere 0 r) :=
    (isCompact_sphere (0 : ℂ) r).image_of_continuousOn
      (hφan.continuousOn.mono sphere_subset_closedBall)
  have hKU : φ '' sphere 0 r ⊆ U := by
    rintro _ ⟨ζ, hζ, rfl⟩
    exact hdiscU ζ (sphere_subset_closedBall hζ)
  have hrad := hU.holomorphic_radius_bound ho hK hKU (q := fun _ => (m : ℂ)) analyticOnNhd_const
    (fun z hz => by
      obtain ⟨ζ, hζ, rfl⟩ := hz
      have : ‖(m : ℂ)‖ = m := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm0]
      rw [this]
      exact (ball_subset_ball (hcircle ζ hζ)).trans
        (by simpa using ball_infDist_subset_compl (x := φ ζ) (s := Uᶜ)))
    (φ 0) hhull
  have hm' : ‖(m : ℂ)‖ = m := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm0]
  rw [hm'] at hrad
  have hUc : Uᶜ.Nonempty := ⟨p, ho.notMem_of_mem_frontier hp⟩
  have hmle : m ≤ infDist (φ 0) Uᶜ := by
    by_contra hlt
    push Not at hlt
    obtain ⟨y, hy, hdy⟩ := (infDist_lt_iff hUc).mp hlt
    exact hy (hrad (by rwa [mem_ball, dist_comm]))
  have hfinal : m ≤ C₁ * (2 * κ * r ^ 2) := hmle.trans hcenter
  rw [hm, hκ] at hfinal
  have hC₁' : C₁ * (2 * (c₂ * (-L) / (8 * C₁)) * r ^ 2) = c₂ * (-L) / 4 * r ^ 2 := by
    field_simp
    ring
  rw [hC₁'] at hfinal
  have : 0 < c₂ * (-L) / 4 * r ^ 2 := by
    have : 0 < -L := by linarith
    positivity
  linarith

section Transport

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Levi pseudoconvexity pulls back along a continuous linear equivalence. -/
theorem IsLeviPseudoconvex.of_image_equiv {U : Set E} (L : E ≃L[ℂ] F)
    (h : IsLeviPseudoconvex (L '' U)) : IsLeviPseudoconvex U := by
  intro p hp ρ V hρ
  have hfr : L p ∈ frontier (L '' U) := by
    have hfr' := L.toHomeomorph.image_frontier U
    rw [ContinuousLinearEquiv.coe_toHomeomorph] at hfr'
    rw [← hfr']
    exact mem_image_of_mem _ hp
  have himg : L.symm ⁻¹' U = L '' U := by
    ext z
    constructor
    · intro hz
      exact ⟨L.symm z, hz, L.apply_symm_apply z⟩
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
  have hdef : IsLocalDefiningFunction (L '' U) (L p) (ρ ∘ L.symm) (univ ∩ L.symm ⁻¹' V) := by
    rw [← himg]
    exact hρ.comp_analytic isOpen_univ (mem_univ _) (L.symm.toContinuousLinearMap.analyticOnNhd _)
      (L.symm_apply_apply p) (by rw [L.symm.fderiv]; exact L.symm.surjective)
  have hcond := h (L p) hfr (ρ ∘ L.symm) _ hdef
  exact (leviCondition_comp_iff hρ (L.symm.toContinuousLinearMap.analyticOnNhd univ _ (mem_univ _))
    (L.symm_apply_apply p) L.symm L.symm.hasFDerivAt).mp hcond

/-- **Levi's theorem.** A domain of holomorphy in a finite-dimensional complex normed space is
Levi pseudoconvex: the Levi form of every local defining function is positive semidefinite on
the complex tangent space at every boundary point. -/
theorem IsDomainOfHolomorphy.isLeviPseudoconvex [FiniteDimensional ℂ E] {U : Set E}
    (hU : IsDomainOfHolomorphy U) (ho : IsOpen U) : IsLeviPseudoconvex U := by
  let L := (Module.finBasis ℂ E).equivFunL
  exact IsLeviPseudoconvex.of_image_equiv L
    ((hU.image_equiv L).isLeviPseudoconvex_fin (L.isOpenMap U ho))

end Transport

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
