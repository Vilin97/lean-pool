/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Analysis.SemiconvexJensen.Jensen.ContactSets

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Jensen Contact-Set Theorem (VolumeEstimates)

Part of the localized Jensen contact-set theorem and the smooth convex
approximation machinery used to prove it. Split from `Jensen.lean`; see the
umbrella module docstring.
-/
@[expose] public noncomputable section

open scoped ContDiff MatrixOrder Topology
open scoped Convolution
open scoped ENNReal

open ContinuousLinearMap MeasureTheory

namespace ViscositySolns

variable {n : Nat}
/--
The gradient image of the Jensen contact set contains a ball around `0`.

In quantified mathematical form, under the hypotheses of the preceding
contact-point selection theorem, if `delta > 0`, then there exists `rho > 0`
such that every `q ∈ ball 0 rho` can be written as `q = -G z` for some
`z ∈ JensenContactSet f x0 r delta`.
-/
theorem exists_pos_radius_ball_subset_neg_gradient_image_jensenContactSet
    {f : Point n -> Real} {x0 : Point n} {r delta : Real} {G : Point n -> Point n}
    (hr : 0 <= r)
    (hdelta : 0 < delta)
    (hfClosed : ContinuousOn f (Metric.closedBall x0 r))
    (hfSphere : ContinuousOn f (Metric.sphere x0 r))
    (hstrict :
      ∀ x : Point n, x ∈ Metric.closedBall x0 r -> dist x x0 = r -> f x < f x0)
    (hderiv :
      ∀ z : Point n, z ∈ Metric.ball x0 r ->
        HasFDerivAt f (gradientLinearMap (G z)) z) :
    ∃ rho : Real, 0 < rho ∧
      Metric.ball (0 : Point n) rho ⊆
        (fun z : Point n => -G z) '' JensenContactSet f x0 r delta := by
  rcases exists_pos_boundary_gap_forall_small_perturbation_exists_contact_gradient
      (n := n) (f := f) (x0 := x0) (r := r) (G := G)
      hr hfClosed hfSphere hstrict hderiv with
    ⟨gamma, hgamma_pos, hcontact⟩
  let a : Real := (n : Real) * r
  let rho : Real := min (delta / 2) (gamma / (2 * (a + 1)))
  have ha_nonneg : 0 <= a := by
    exact mul_nonneg (Nat.cast_nonneg n) hr
  have ha1_pos : 0 < a + 1 := by
    linarith
  have hden_pos : 0 < 2 * (a + 1) := by positivity
  have hgamma_half_lt : gamma / 2 < gamma := by linarith
  have hrho_pos : 0 < rho := by
    dsimp [rho]
    exact lt_min (half_pos hdelta) (div_pos hgamma_pos hden_pos)
  refine ⟨rho, hrho_pos, ?_⟩
  intro q hq
  have hqnorm : ‖q‖ < rho := by
    simpa [Metric.mem_ball, dist_eq_norm] using hq
  have hq_delta : q ∈ Metric.ball (0 : Point n) delta := by
    have hrho_le : rho <= delta / 2 := min_le_left _ _
    have hnorm_lt_half : ‖q‖ < delta / 2 := lt_of_lt_of_le hqnorm hrho_le
    have hnorm_lt_delta : ‖q‖ < delta := by linarith
    simpa [Metric.mem_ball, dist_eq_norm] using hnorm_lt_delta
  have hq_gamma_bound : ‖q‖ < gamma / (2 * (a + 1)) := by
    exact lt_of_lt_of_le hqnorm (min_le_right _ _)
  have hmul_bound : a * ‖q‖ < gamma / 2 := by
    have hmul_lt :
        (a + 1) * ‖q‖ < (a + 1) * (gamma / (2 * (a + 1))) :=
      mul_lt_mul_of_pos_left hq_gamma_bound ha1_pos
    have hright : (a + 1) * (gamma / (2 * (a + 1))) = gamma / 2 := by
      field_simp [ha1_pos.ne']
    have hle : a * ‖q‖ <= (a + 1) * ‖q‖ := by
      nlinarith [norm_nonneg q]
    nlinarith
  have hq_small : (n : Real) * ‖q‖ * r < gamma := by
    have hrewrite : (n : Real) * ‖q‖ * r = a * ‖q‖ := by
      dsimp [a]
      ring
    rw [hrewrite]
    exact lt_trans hmul_bound hgamma_half_lt
  rcases hcontact q hq_delta hq_small with ⟨z, hzContact, _hmax, _hzBall, hgrad⟩
  refine ⟨z, hzContact, ?_⟩
  have hq_eq : -G z = q := by
    rw [neg_eq_iff_add_eq_zero]
    simpa [add_comm] using hgrad
  exact hq_eq

/--
The gradient image of the closed-ball global contact set contains a ball
around `0`.

In quantified mathematical form, under the same hypotheses as
`exists_pos_radius_ball_subset_neg_gradient_image_jensenContactSet`, if
`delta > 0`, then there exists `rho > 0` such that every `q ∈ ball 0 rho`
can be written as `q = -G z` for some
`z ∈ JensenGlobalContactSet f x0 r delta`.
-/
theorem exists_pos_radius_ball_subset_neg_gradient_image_jensenGlobalContactSet
    {f : Point n -> Real} {x0 : Point n} {r delta : Real} {G : Point n -> Point n}
    (hr : 0 <= r)
    (hdelta : 0 < delta)
    (hfClosed : ContinuousOn f (Metric.closedBall x0 r))
    (hfSphere : ContinuousOn f (Metric.sphere x0 r))
    (hstrict :
      ∀ x : Point n, x ∈ Metric.closedBall x0 r -> dist x x0 = r -> f x < f x0)
    (hderiv :
      ∀ z : Point n, z ∈ Metric.ball x0 r ->
        HasFDerivAt f (gradientLinearMap (G z)) z) :
    ∃ rho : Real, 0 < rho ∧
      Metric.ball (0 : Point n) rho ⊆
        (fun z : Point n => -G z) '' JensenGlobalContactSet f x0 r delta := by
  rcases exists_pos_boundary_gap_forall_small_perturbation_exists_contact_gradient
      (n := n) (f := f) (x0 := x0) (r := r) (G := G)
      hr hfClosed hfSphere hstrict hderiv with
    ⟨gamma, hgamma_pos, hcontact⟩
  let a : Real := (n : Real) * r
  let rho : Real := min (delta / 2) (gamma / (2 * (a + 1)))
  have ha_nonneg : 0 <= a := by
    exact mul_nonneg (Nat.cast_nonneg n) hr
  have ha1_pos : 0 < a + 1 := by
    linarith
  have hden_pos : 0 < 2 * (a + 1) := by positivity
  have hgamma_half_lt : gamma / 2 < gamma := by linarith
  have hrho_pos : 0 < rho := by
    dsimp [rho]
    exact lt_min (half_pos hdelta) (div_pos hgamma_pos hden_pos)
  refine ⟨rho, hrho_pos, ?_⟩
  intro q hq
  have hqnorm : ‖q‖ < rho := by
    simpa [Metric.mem_ball, dist_eq_norm] using hq
  have hq_delta : q ∈ Metric.ball (0 : Point n) delta := by
    have hrho_le : rho <= delta / 2 := min_le_left _ _
    have hnorm_lt_half : ‖q‖ < delta / 2 := lt_of_lt_of_le hqnorm hrho_le
    have hnorm_lt_delta : ‖q‖ < delta := by linarith
    simpa [Metric.mem_ball, dist_eq_norm] using hnorm_lt_delta
  have hq_gamma_bound : ‖q‖ < gamma / (2 * (a + 1)) := by
    exact lt_of_lt_of_le hqnorm (min_le_right _ _)
  have hmul_bound : a * ‖q‖ < gamma / 2 := by
    have hmul_lt :
        (a + 1) * ‖q‖ < (a + 1) * (gamma / (2 * (a + 1))) :=
      mul_lt_mul_of_pos_left hq_gamma_bound ha1_pos
    have hright : (a + 1) * (gamma / (2 * (a + 1))) = gamma / 2 := by
      field_simp [ha1_pos.ne']
    have hle : a * ‖q‖ <= (a + 1) * ‖q‖ := by
      nlinarith [norm_nonneg q]
    nlinarith
  have hq_small : (n : Real) * ‖q‖ * r < gamma := by
    have hrewrite : (n : Real) * ‖q‖ * r = a * ‖q‖ := by
      dsimp [a]
      ring
    rw [hrewrite]
    exact lt_trans hmul_bound hgamma_half_lt
  rcases hcontact q hq_delta hq_small with ⟨z, _hzContact, hmax, hzBall, hgrad⟩
  refine ⟨z, ?_, ?_⟩
  · exact ⟨hzBall, q, hq_delta, hmax⟩
  · have hq_eq : -G z = q := by
      rw [neg_eq_iff_add_eq_zero]
      simpa [add_comm] using hgrad
    exact hq_eq

/--
The explicit boundary-gap radius used in the smooth proof of Jensen's lemma.

In quantified mathematical form, assume every boundary point of
`closedBall x0 r` satisfies `f x ≤ f x0 - gamma`, with `gamma > 0`. If
`delta > 0`, then every vector in

`ball 0 (min (delta / 2) (gamma / (2 * ((n : Real) * r + 1))))`

is equal to `-G z` for some `z ∈ JensenGlobalContactSet f x0 r delta`.
-/
theorem ball_subset_neg_gradient_image_jensenGlobalContactSet_of_boundary_gap
    {f : Point n -> Real} {x0 : Point n} {r delta gamma : Real}
    {G : Point n -> Point n}
    (hr : 0 <= r)
    (hdelta : 0 < delta)
    (hgamma : 0 < gamma)
    (hfClosed : ContinuousOn f (Metric.closedBall x0 r))
    (hgap :
      ∀ y : Point n, y ∈ Metric.closedBall x0 r -> dist y x0 = r ->
        f y <= f x0 - gamma)
    (hderiv :
      ∀ z : Point n, z ∈ Metric.ball x0 r ->
        HasFDerivAt f (gradientLinearMap (G z)) z) :
    Metric.ball (0 : Point n)
        (min (delta / 2) (gamma / (2 * ((n : Real) * r + 1)))) ⊆
      (fun z : Point n => -G z) '' JensenGlobalContactSet f x0 r delta := by
  let a : Real := (n : Real) * r
  let rho : Real := min (delta / 2) (gamma / (2 * (a + 1)))
  have ha_nonneg : 0 <= a := by
    exact mul_nonneg (Nat.cast_nonneg n) hr
  have ha1_pos : 0 < a + 1 := by
    linarith
  have hgamma_half_lt : gamma / 2 < gamma := by
    linarith
  intro q hq
  have hqnorm : ‖q‖ < rho := by
    simpa [rho, a, Metric.mem_ball, dist_eq_norm] using hq
  have hq_delta : q ∈ Metric.ball (0 : Point n) delta := by
    have hrho_le : rho <= delta / 2 := min_le_left _ _
    have hnorm_lt_half : ‖q‖ < delta / 2 := lt_of_lt_of_le hqnorm hrho_le
    have hnorm_lt_delta : ‖q‖ < delta := by linarith
    simpa [Metric.mem_ball, dist_eq_norm] using hnorm_lt_delta
  have hq_gamma_bound : ‖q‖ < gamma / (2 * (a + 1)) := by
    exact lt_of_lt_of_le hqnorm (min_le_right _ _)
  have hmul_bound : a * ‖q‖ < gamma / 2 := by
    have hmul_lt :
        (a + 1) * ‖q‖ < (a + 1) * (gamma / (2 * (a + 1))) :=
      mul_lt_mul_of_pos_left hq_gamma_bound ha1_pos
    have hright : (a + 1) * (gamma / (2 * (a + 1))) = gamma / 2 := by
      field_simp [ha1_pos.ne']
    have hle : a * ‖q‖ <= (a + 1) * ‖q‖ := by
      nlinarith [norm_nonneg q]
    nlinarith
  have hq_small : (n : Real) * ‖q‖ * r < gamma := by
    have hrewrite : (n : Real) * ‖q‖ * r = a * ‖q‖ := by
      dsimp [a]
      ring
    rw [hrewrite]
    exact lt_trans hmul_bound hgamma_half_lt
  rcases exists_mem_jensenContactSet_of_boundary_gap
      (n := n) (f := f) (x0 := x0) (p := q)
      (r := r) (gamma := gamma) (delta := delta)
      hr hfClosed hgap hq_small hq_delta with
    ⟨z, _hzContact, hmax, hzBall⟩
  have hlocal : IsLocalMax (linearPerturbation f q) z :=
    hmax.isLocalMax (Metric.closedBall_mem_nhds_of_mem hzBall)
  have hgrad :
      G z + q = 0 :=
    gradient_add_eq_zero_of_isLocalMax_linearPerturbation_hasFDerivAt
      (n := n) hlocal (hderiv z hzBall)
  refine ⟨z, ?_, ?_⟩
  · exact ⟨hzBall, q, hq_delta, hmax⟩
  · rw [neg_eq_iff_add_eq_zero]
    simpa [add_comm] using hgrad

/--
A measure-theoretic consequence used in the smooth part of Jensen's lemma.

In quantified mathematical form, let `S ⊆ R^n`, let `G : R^n -> R^n`, and
assume that `G` is differentiable at every point of `S`, relative to `S`. If
there are `c ∈ R^n` and `rho > 0` such that
`ball c rho ⊆ G '' S`, then `S` has positive Lebesgue measure.

The proof uses the standard theorem, already in mathlib, that a differentiable
map from `R^n` to `R^n` sends every Lebesgue-null set to a Lebesgue-null set.
-/
theorem volume_pos_of_ball_subset_image_of_differentiableOn
    {S : Set (Point n)} {G : Point n -> Point n} {c : Point n} {rho : Real}
    (hG : DifferentiableOn Real G S)
    (hrho : 0 < rho)
    (hsubset : Metric.ball c rho ⊆ G '' S) :
    0 < volume S := by
  by_contra hnot
  have hSzero : volume S = 0 := by
    exact nonpos_iff_eq_zero.mp (not_lt.mp hnot)
  have hImageZero : volume (G '' S) = 0 :=
    MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero
      (μ := volume) hG hSzero
  have hball_le : volume (Metric.ball c rho) <= volume (G '' S) :=
    measure_mono hsubset
  have hball_pos : 0 < volume (Metric.ball c rho) :=
    Metric.measure_ball_pos volume c hrho
  rw [hImageZero] at hball_le
  exact (not_lt_of_ge hball_le) hball_pos

/--
A quantitative image-measure lower bound.

In quantified mathematical form, let `S ⊆ R^n`, let `G : R^n -> R^n`, and
let `M ∈ [0,∞]` satisfy `M ≠ 0` and `M ≠ ∞`. If `ball c rho ⊆ G '' S` and
`volume (G '' S) ≤ M * volume S`, then
`volume (ball c rho) / M ≤ volume S`.
-/
theorem volume_ball_div_le_of_ball_subset_image_of_image_le_mul
    {S : Set (Point n)} {G : Point n -> Point n} {c : Point n} {rho : Real}
    {M : ℝ≥0∞}
    (hM0 : M ≠ 0)
    (hMtop : M ≠ (∞ : ℝ≥0∞))
    (hsubset : Metric.ball c rho ⊆ G '' S)
    (himage : volume (G '' S) <= M * volume S) :
    volume (Metric.ball c rho) / M <= volume S := by
  have hball_le : volume (Metric.ball c rho) <= M * volume S :=
    (measure_mono hsubset).trans himage
  exact (ENNReal.div_le_iff hM0 hMtop).2 (by
    simpa [mul_comm] using hball_le)

/--
A positive-measure consequence of the quantitative image-measure lower bound.

In quantified mathematical form, under the hypotheses of
`volume_ball_div_le_of_ball_subset_image_of_image_le_mul`, if `rho > 0`, then
`S` has positive Lebesgue measure.
-/
theorem volume_pos_of_ball_subset_image_of_image_le_mul
    {S : Set (Point n)} {G : Point n -> Point n} {c : Point n} {rho : Real}
    {M : ℝ≥0∞}
    (hrho : 0 < rho)
    (hM0 : M ≠ 0)
    (hMtop : M ≠ (∞ : ℝ≥0∞))
    (hsubset : Metric.ball c rho ⊆ G '' S)
    (himage : volume (G '' S) <= M * volume S) :
    0 < volume S := by
  have hball_pos : 0 < volume (Metric.ball c rho) :=
    Metric.measure_ball_pos volume c hrho
  have hdiv_pos : 0 < volume (Metric.ball c rho) / M :=
    ENNReal.div_pos hball_pos.ne' hMtop
  exact lt_of_lt_of_le hdiv_pos
    (volume_ball_div_le_of_ball_subset_image_of_image_le_mul
      (n := n) (S := S) (G := G) (c := c) (rho := rho) (M := M)
      hM0 hMtop hsubset himage)

/--
A quantitative lower bound from the Jacobian image-measure estimate.

In quantified mathematical form, let `S ⊆ R^n`, let `G : R^n -> R^n`, and
let `G' x` be the Fréchet derivative of `G` at `x` relative to `S` for every
`x ∈ S`. Suppose `S` is measurable, `ball c rho ⊆ G '' S`, and
`ofReal |det (G' x)| ≤ M` for every `x ∈ S`, where `M ≠ 0` and `M ≠ ∞`.
Then `volume (ball c rho) / M ≤ volume S`.
-/
theorem volume_ball_div_le_of_ball_subset_image_of_hasFDerivWithinAt_det_le
    {S : Set (Point n)} {G : Point n -> Point n}
    {G' : Point n -> Point n →L[Real] Point n}
    {c : Point n} {rho : Real} {M : ℝ≥0∞}
    (hSmeas : MeasurableSet S)
    (hG' : ∀ x : Point n, x ∈ S -> HasFDerivWithinAt G (G' x) S x)
    (hM0 : M ≠ 0)
    (hMtop : M ≠ (∞ : ℝ≥0∞))
    (hdet : ∀ x : Point n, x ∈ S -> ENNReal.ofReal |(G' x).det| <= M)
    (hsubset : Metric.ball c rho ⊆ G '' S) :
    volume (Metric.ball c rho) / M <= volume S := by
  have hImageJac :
      volume (G '' S) <=
        ∫⁻ x in S, ENNReal.ofReal |(G' x).det| ∂volume :=
    MeasureTheory.addHaar_image_le_lintegral_abs_det_fderiv
      (μ := volume) hSmeas hG'
  have hIntegralBound :
      (∫⁻ x in S, ENNReal.ofReal |(G' x).det| ∂volume) <= M * volume S := by
    calc
      (∫⁻ x in S, ENNReal.ofReal |(G' x).det| ∂volume)
          <= ∫⁻ _x in S, M ∂volume := by
            apply lintegral_mono_ae
            filter_upwards [ae_restrict_mem hSmeas] with x hx
            exact hdet x hx
      _ = M * volume S := by
        simp
  exact volume_ball_div_le_of_ball_subset_image_of_image_le_mul
    (n := n) (S := S) (G := G) (c := c) (rho := rho) (M := M)
    hM0 hMtop hsubset (hImageJac.trans hIntegralBound)

/--
Quantitative closed-ball global contact-set lower bound with an explicit
boundary-gap radius.

In quantified mathematical form, assume every boundary point of
`closedBall x0 r` satisfies `f x ≤ f x0 - gamma`, with `gamma > 0`. Let
`rho = min (delta / 2) (gamma / (2 * ((n : Real) * r + 1)))`. If the
closed-ball global contact set is measurable, if `z ↦ -G z` has derivative
`G' z` at every point of this contact set relative to the contact set, and if
`ofReal |det (G' z)| ≤ M` on the contact set, where `M ≠ 0` and `M ≠ ∞`, then

`volume (ball 0 rho) / M ≤
 volume (JensenGlobalContactSet f x0 r delta)`.
-/
theorem volume_explicit_ball_div_le_jensenGlobalContactSet_of_boundary_gap_det_le
    {f : Point n -> Real} {x0 : Point n} {r delta gamma : Real}
    {G : Point n -> Point n} {G' : Point n -> Point n →L[Real] Point n}
    {M : ℝ≥0∞}
    (hr : 0 <= r)
    (hdelta : 0 < delta)
    (hgamma : 0 < gamma)
    (hfClosed : ContinuousOn f (Metric.closedBall x0 r))
    (hgap :
      ∀ y : Point n, y ∈ Metric.closedBall x0 r -> dist y x0 = r ->
        f y <= f x0 - gamma)
    (hderiv :
      ∀ z : Point n, z ∈ Metric.ball x0 r ->
        HasFDerivAt f (gradientLinearMap (G z)) z)
    (hContactMeas : MeasurableSet (JensenGlobalContactSet f x0 r delta))
    (hM0 : M ≠ 0)
    (hMtop : M ≠ (∞ : ℝ≥0∞))
    (hG' :
      ∀ z : Point n, z ∈ JensenGlobalContactSet f x0 r delta ->
        HasFDerivWithinAt (fun w : Point n => -G w) (G' z)
          (JensenGlobalContactSet f x0 r delta) z)
    (hdet :
      ∀ z : Point n, z ∈ JensenGlobalContactSet f x0 r delta ->
        ENNReal.ofReal |(G' z).det| <= M) :
    volume (Metric.ball (0 : Point n)
        (min (delta / 2) (gamma / (2 * ((n : Real) * r + 1))))) / M <=
      volume (JensenGlobalContactSet f x0 r delta) := by
  have hsubset :
      Metric.ball (0 : Point n)
          (min (delta / 2) (gamma / (2 * ((n : Real) * r + 1)))) ⊆
        (fun z : Point n => -G z) '' JensenGlobalContactSet f x0 r delta :=
    ball_subset_neg_gradient_image_jensenGlobalContactSet_of_boundary_gap
      (n := n) (f := f) (x0 := x0) (r := r) (delta := delta)
      (gamma := gamma) (G := G)
      hr hdelta hgamma hfClosed hgap hderiv
  exact volume_ball_div_le_of_ball_subset_image_of_hasFDerivWithinAt_det_le
    (n := n)
    (S := JensenGlobalContactSet f x0 r delta)
    (G := fun z : Point n => -G z)
    (G' := G')
    (c := 0)
    (rho := min (delta / 2) (gamma / (2 * ((n : Real) * r + 1))))
    (M := M)
    hContactMeas hG' hM0 hMtop hdet hsubset

/--
Uniform convergence preserves a positive boundary gap after discarding
finitely many terms.

In quantified mathematical form, assume every boundary point of
`closedBall x0 r` satisfies `f x ≤ f x0 - gamma`, with `gamma > 0`, and assume
`f_m -> f` uniformly on `closedBall x0 r`. Then there exists `N` such that
for every `m ≥ N` and every boundary point `x`,

`f_m x ≤ f_m x0 - gamma / 2`.
-/
theorem eventually_boundary_gap_of_uniformOn_closedBall
    {f : Point n -> Real} {fseq : Nat -> Point n -> Real}
    {x0 : Point n} {r gamma : Real}
    (hr : 0 <= r)
    (hgamma : 0 < gamma)
    (hgap :
      ∀ x : Point n, x ∈ Metric.closedBall x0 r -> dist x x0 = r ->
        f x <= f x0 - gamma)
    (hunif :
      ∀ eps : Real, 0 < eps ->
        ∃ N : Nat, ∀ m : Nat, N <= m ->
          ∀ z : Point n, z ∈ Metric.closedBall x0 r ->
            |fseq m z - f z| <= eps) :
    ∃ N : Nat,
      ∀ m : Nat, N <= m ->
        ∀ x : Point n, x ∈ Metric.closedBall x0 r -> dist x x0 = r ->
          fseq m x <= fseq m x0 - gamma / 2 := by
  rcases hunif (gamma / 4) (by linarith) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro m hm x hx hboundary
  have hx0 : x0 ∈ Metric.closedBall x0 r := Metric.mem_closedBall_self hr
  have hx_bound := hN m hm x hx
  have hx0_bound := hN m hm x0 hx0
  have hx_upper : fseq m x <= f x + gamma / 4 := by
    have hle_abs : fseq m x - f x <= |fseq m x - f x| := le_abs_self _
    linarith
  have hx0_lower : f x0 - gamma / 4 <= fseq m x0 := by
    have hneg_abs : -|fseq m x0 - f x0| <= fseq m x0 - f x0 := neg_abs_le _
    linarith
  have hfgap := hgap x hx hboundary
  linarith

/--
A positive-measure consequence of the Jacobian image-measure estimate.

In quantified mathematical form, under the hypotheses of
`volume_ball_div_le_of_ball_subset_image_of_hasFDerivWithinAt_det_le`, if
`rho > 0`, then `S` has positive Lebesgue measure.
-/
theorem volume_pos_of_ball_subset_image_of_hasFDerivWithinAt_det_le
    {S : Set (Point n)} {G : Point n -> Point n}
    {G' : Point n -> Point n →L[Real] Point n}
    {c : Point n} {rho : Real} {M : ℝ≥0∞}
    (hSmeas : MeasurableSet S)
    (hG' : ∀ x : Point n, x ∈ S -> HasFDerivWithinAt G (G' x) S x)
    (hrho : 0 < rho)
    (hM0 : M ≠ 0)
    (hMtop : M ≠ (∞ : ℝ≥0∞))
    (hdet : ∀ x : Point n, x ∈ S -> ENNReal.ofReal |(G' x).det| <= M)
    (hsubset : Metric.ball c rho ⊆ G '' S) :
    0 < volume S := by
  have hball_pos : 0 < volume (Metric.ball c rho) :=
    Metric.measure_ball_pos volume c hrho
  have hdiv_pos : 0 < volume (Metric.ball c rho) / M :=
    ENNReal.div_pos hball_pos.ne' hMtop
  exact lt_of_lt_of_le hdiv_pos
    (volume_ball_div_le_of_ball_subset_image_of_hasFDerivWithinAt_det_le
      (n := n) (S := S) (G := G) (G' := G') (c := c) (rho := rho) (M := M)
      hSmeas hG' hM0 hMtop hdet hsubset)

/--
Measure lower bounds pass from a sequence of sets to its limsup.

In quantified mathematical form, let `E m` be a sequence of measurable
subsets of a measure space, and suppose all `E m` are contained in a set `B`
with finite measure. If a set `K` contains

`⋂ n, ⋃ m, ⋃ (_ : n ≤ m), E m`,

and if `c ≤ μ (E m)` for every `m`, then `c ≤ μ K`.
-/
theorem measure_limsup_le_of_forall_measure_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E : Nat -> Set α} {B K : Set α} {c : ℝ≥0∞}
    (hEmeas : ∀ m : Nat, MeasurableSet (E m))
    (hBfinite : μ B ≠ (∞ : ℝ≥0∞))
    (hsubB : ∀ m : Nat, E m ⊆ B)
    (hlimsup :
      (⋂ n : Nat, ⋃ m : Nat, ⋃ (_hm : n <= m), E m) ⊆ K)
    (hlower : ∀ m : Nat, c <= μ (E m)) :
    c <= μ K := by
  let U : Nat -> Set α := fun n => ⋃ m : Nat, ⋃ (_hm : n <= m), E m
  have hUmeas : ∀ n : Nat, NullMeasurableSet (U n) μ := by
    intro n
    dsimp [U]
    exact (MeasurableSet.iUnion fun m =>
      MeasurableSet.iUnion fun _hm => hEmeas m).nullMeasurableSet
  have hUanti : Antitone U := by
    intro n k hnk
    dsimp [U]
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨m, hm⟩
    rcases Set.mem_iUnion.mp hm with ⟨hnm, hxE⟩
    exact Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨le_trans hnk hnm, hxE⟩⟩
  have hUfinite : ∃ n : Nat, μ (U n) ≠ (∞ : ℝ≥0∞) := by
    refine ⟨0, ?_⟩
    have hUB : U 0 ⊆ B := by
      dsimp [U]
      intro x hx
      rcases Set.mem_iUnion.mp hx with ⟨m, hm⟩
      rcases Set.mem_iUnion.mp hm with ⟨_h0m, hxE⟩
      exact hsubB m hxE
    exact ne_top_of_le_ne_top hBfinite (measure_mono hUB)
  have hTendsto :
      Filter.Tendsto (fun n : Nat => μ (U n)) Filter.atTop
        (𝓝 (μ (⋂ n : Nat, U n))) := by
    simpa [Function.comp_def] using
      (tendsto_measure_iInter_atTop (μ := μ) (s := U) hUmeas hUanti hUfinite)
  have hUlower : ∀ n : Nat, c <= μ (U n) := by
    intro n
    have hEnU : E n ⊆ U n := by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨le_rfl, hx⟩⟩
    exact (hlower n).trans (measure_mono hEnU)
  have hlimsup_lower : c <= μ (⋂ n : Nat, U n) :=
    ge_of_tendsto' hTendsto hUlower
  exact hlimsup_lower.trans (measure_mono (by simpa [U] using hlimsup))

/--
Positive measure passes from a sequence of uniformly positive measurable sets
to any set containing their limsup.

In quantified mathematical form, under the hypotheses of
`measure_limsup_le_of_forall_measure_le`, if `0 < c`, then `0 < μ K`.
-/
theorem measure_pos_of_limsup_subset_of_forall_measure_ge
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {E : Nat -> Set α} {B K : Set α} {c : ℝ≥0∞}
    (hc : 0 < c)
    (hEmeas : ∀ m : Nat, MeasurableSet (E m))
    (hBfinite : μ B ≠ (∞ : ℝ≥0∞))
    (hsubB : ∀ m : Nat, E m ⊆ B)
    (hlimsup :
      (⋂ n : Nat, ⋃ m : Nat, ⋃ (_hm : n <= m), E m) ⊆ K)
    (hlower : ∀ m : Nat, c <= μ (E m)) :
    0 < μ K :=
  lt_of_lt_of_le hc
    (measure_limsup_le_of_forall_measure_le
      (μ := μ) hEmeas hBfinite hsubB hlimsup hlower)

/--
The limsup measure passage specialized to Jensen contact sets.

In quantified mathematical form, let `f_m : R^n -> R` be a sequence of
functions and let `f : R^n -> R`. Suppose there exists `c > 0` such that, for
every natural number `m`, the set `JensenContactSet (f_m) x0 r delta` is
measurable and has Lebesgue measure at least `c`. If

`⋂ n, ⋃ m, ⋃ (_ : n ≤ m), JensenContactSet (f_m) x0 r delta`

is contained in `JensenContactSet f x0 r delta`, then
`JensenContactSet f x0 r delta` has positive Lebesgue measure.
-/
theorem volume_pos_jensenContactSet_of_limsup_contact_sets
    {f : Point n -> Real} {fseq : Nat -> Point n -> Real}
    {x0 : Point n} {r delta : Real} {c : ℝ≥0∞}
    (hc : 0 < c)
    (hmeas :
      ∀ m : Nat, MeasurableSet (JensenContactSet (fseq m) x0 r delta))
    (hlimsup :
      (⋂ n : Nat, ⋃ m : Nat, ⋃ (_hm : n <= m),
        JensenContactSet (fseq m) x0 r delta) ⊆
        JensenContactSet f x0 r delta)
    (hlower :
      ∀ m : Nat, c <= volume (JensenContactSet (fseq m) x0 r delta)) :
    0 < volume (JensenContactSet f x0 r delta) := by
  refine measure_pos_of_limsup_subset_of_forall_measure_ge
    (μ := volume) (E := fun m : Nat => JensenContactSet (fseq m) x0 r delta)
    (B := Metric.closedBall x0 r) (K := JensenContactSet f x0 r delta)
    hc hmeas ?_ ?_ hlimsup hlower
  · exact measure_closedBall_lt_top.ne
  · intro m
    exact JensenContactSet.subset_closedBall (fseq m) x0 r delta

/--
Positive measure of the Jensen contact set from differentiability of the
gradient image map.

In quantified mathematical form, assume the hypotheses which give contact
points for all sufficiently small linear perturbations, and assume that
`f` is differentiable on `ball x0 r` with gradient `G`. If the map
`z ↦ -G z` is differentiable at every point of
`JensenContactSet f x0 r delta`, relative to that contact set, then
`JensenContactSet f x0 r delta` has positive Lebesgue measure.
-/
theorem volume_pos_jensenContactSet_of_differentiableOn_neg_gradient
    {f : Point n -> Real} {x0 : Point n} {r delta : Real} {G : Point n -> Point n}
    (hr : 0 <= r)
    (hdelta : 0 < delta)
    (hfClosed : ContinuousOn f (Metric.closedBall x0 r))
    (hfSphere : ContinuousOn f (Metric.sphere x0 r))
    (hstrict :
      ∀ x : Point n, x ∈ Metric.closedBall x0 r -> dist x x0 = r -> f x < f x0)
    (hderiv :
      ∀ z : Point n, z ∈ Metric.ball x0 r ->
        HasFDerivAt f (gradientLinearMap (G z)) z)
    (hG :
      DifferentiableOn Real (fun z : Point n => -G z)
        (JensenContactSet f x0 r delta)) :
    0 < volume (JensenContactSet f x0 r delta) := by
  rcases exists_pos_radius_ball_subset_neg_gradient_image_jensenContactSet
      (n := n) (f := f) (x0 := x0) (r := r) (delta := delta) (G := G)
      hr hdelta hfClosed hfSphere hstrict hderiv with
    ⟨rho, hrho_pos, hsubset⟩
  exact volume_pos_of_ball_subset_image_of_differentiableOn
    (n := n)
    (S := JensenContactSet f x0 r delta)
    (G := fun z : Point n => -G z)
    (c := 0) (rho := rho)
    hG hrho_pos hsubset

/--
Quantitative Jensen contact-set lower bound from a determinant bound for the
negative-gradient map.

In quantified mathematical form, assume the hypotheses which give contact
points for all sufficiently small linear perturbations, and let `G` be the
gradient of `f` on `ball x0 r`. Suppose that `JensenContactSet f x0 r delta`
is measurable, that `z ↦ -G z` has derivative `G' z` at every contact point
relative to the contact set, and that
`ofReal |det (G' z)| ≤ M` at every contact point, where `M ≠ 0` and
`M ≠ ∞`. Then there exists `rho > 0` such that
`volume (ball 0 rho) / M ≤ volume (JensenContactSet f x0 r delta)`.
-/
theorem exists_pos_radius_volume_ball_div_le_jensenContactSet_of_neg_gradient_det_le
    {f : Point n -> Real} {x0 : Point n} {r delta : Real}
    {G : Point n -> Point n} {G' : Point n -> Point n →L[Real] Point n}
    {M : ℝ≥0∞}
    (hr : 0 <= r)
    (hdelta : 0 < delta)
    (hfClosed : ContinuousOn f (Metric.closedBall x0 r))
    (hfSphere : ContinuousOn f (Metric.sphere x0 r))
    (hstrict :
      ∀ x : Point n, x ∈ Metric.closedBall x0 r -> dist x x0 = r -> f x < f x0)
    (hderiv :
      ∀ z : Point n, z ∈ Metric.ball x0 r ->
        HasFDerivAt f (gradientLinearMap (G z)) z)
    (hContactMeas : MeasurableSet (JensenContactSet f x0 r delta))
    (hM0 : M ≠ 0)
    (hMtop : M ≠ (∞ : ℝ≥0∞))
    (hG' :
      ∀ z : Point n, z ∈ JensenContactSet f x0 r delta ->
        HasFDerivWithinAt (fun w : Point n => -G w) (G' z)
          (JensenContactSet f x0 r delta) z)
    (hdet :
      ∀ z : Point n, z ∈ JensenContactSet f x0 r delta ->
        ENNReal.ofReal |(G' z).det| <= M) :
    ∃ rho : Real,
      0 < rho ∧
        volume (Metric.ball (0 : Point n) rho) / M <=
          volume (JensenContactSet f x0 r delta) := by
  rcases exists_pos_radius_ball_subset_neg_gradient_image_jensenContactSet
      (n := n) (f := f) (x0 := x0) (r := r) (delta := delta) (G := G)
      hr hdelta hfClosed hfSphere hstrict hderiv with
    ⟨rho, hrho_pos, hsubset⟩
  refine ⟨rho, hrho_pos, ?_⟩
  exact volume_ball_div_le_of_ball_subset_image_of_hasFDerivWithinAt_det_le
    (n := n)
    (S := JensenContactSet f x0 r delta)
    (G := fun z : Point n => -G z)
    (G' := G')
    (c := 0) (rho := rho) (M := M)
    hContactMeas hG' hM0 hMtop hdet hsubset

/--
Quantitative Jensen lower bound for the closed-ball global contact set from a
determinant bound for the negative-gradient map.

In quantified mathematical form, assume the hypotheses which give closed-ball
maximizers for all sufficiently small linear perturbations, and let `G` be the
gradient of `f` on `ball x0 r`. Suppose that
`JensenGlobalContactSet f x0 r delta` is measurable, that `z ↦ -G z` has
derivative `G' z` at every global contact point relative to the global contact
set, and that `ofReal |det (G' z)| ≤ M` at every global contact point, where
`M ≠ 0` and `M ≠ ∞`. Then there exists `rho > 0` such that
`volume (ball 0 rho) / M ≤ volume (JensenGlobalContactSet f x0 r delta)`.
-/
theorem exists_pos_radius_volume_ball_div_le_jensenGlobalContactSet_of_neg_gradient_det_le
    {f : Point n -> Real} {x0 : Point n} {r delta : Real}
    {G : Point n -> Point n} {G' : Point n -> Point n →L[Real] Point n}
    {M : ℝ≥0∞}
    (hr : 0 <= r)
    (hdelta : 0 < delta)
    (hfClosed : ContinuousOn f (Metric.closedBall x0 r))
    (hfSphere : ContinuousOn f (Metric.sphere x0 r))
    (hstrict :
      ∀ x : Point n, x ∈ Metric.closedBall x0 r -> dist x x0 = r -> f x < f x0)
    (hderiv :
      ∀ z : Point n, z ∈ Metric.ball x0 r ->
        HasFDerivAt f (gradientLinearMap (G z)) z)
    (hContactMeas : MeasurableSet (JensenGlobalContactSet f x0 r delta))
    (hM0 : M ≠ 0)
    (hMtop : M ≠ (∞ : ℝ≥0∞))
    (hG' :
      ∀ z : Point n, z ∈ JensenGlobalContactSet f x0 r delta ->
        HasFDerivWithinAt (fun w : Point n => -G w) (G' z)
          (JensenGlobalContactSet f x0 r delta) z)
    (hdet :
      ∀ z : Point n, z ∈ JensenGlobalContactSet f x0 r delta ->
        ENNReal.ofReal |(G' z).det| <= M) :
    ∃ rho : Real,
      0 < rho ∧
        volume (Metric.ball (0 : Point n) rho) / M <=
          volume (JensenGlobalContactSet f x0 r delta) := by
  rcases exists_pos_radius_ball_subset_neg_gradient_image_jensenGlobalContactSet
      (n := n) (f := f) (x0 := x0) (r := r) (delta := delta) (G := G)
      hr hdelta hfClosed hfSphere hstrict hderiv with
    ⟨rho, hrho_pos, hsubset⟩
  refine ⟨rho, hrho_pos, ?_⟩
  exact volume_ball_div_le_of_ball_subset_image_of_hasFDerivWithinAt_det_le
    (n := n)
    (S := JensenGlobalContactSet f x0 r delta)
    (G := fun z : Point n => -G z)
    (G' := G')
    (c := 0) (rho := rho) (M := M)
    hContactMeas hG' hM0 hMtop hdet hsubset

/--
Quantitative Jensen lower bound for the closed-ball global contact set when
the gradient is continuous.

In quantified mathematical form, under the smooth hypotheses used in Jensen's
lemma, suppose `Df = G` on `ball x0 r`, the map `G` is continuous, the map
`z ↦ -G z` has derivative `G' z` at every global contact point relative to
the global contact set, and `ofReal |det (G' z)| ≤ M` on the global contact
set, where `M ≠ 0` and `M ≠ ∞`. Then there exists `rho > 0` such that
`volume (ball 0 rho) / M ≤ volume (JensenGlobalContactSet f x0 r delta)`.
-/
theorem exists_pos_radius_volume_ball_div_le_jensenGlobalContactSet_of_continuous_gradient_det_le
    {f : Point n -> Real} {x0 : Point n} {r delta : Real}
    {G : Point n -> Point n} {G' : Point n -> Point n →L[Real] Point n}
    {M : ℝ≥0∞}
    (hr : 0 <= r)
    (hdelta : 0 < delta)
    (hf : Continuous f)
    (hG : Continuous G)
    (hstrict :
      ∀ x : Point n, x ∈ Metric.closedBall x0 r -> dist x x0 = r -> f x < f x0)
    (hderiv :
      ∀ z : Point n, z ∈ Metric.ball x0 r ->
        HasFDerivAt f (gradientLinearMap (G z)) z)
    (hM0 : M ≠ 0)
    (hMtop : M ≠ (∞ : ℝ≥0∞))
    (hG' :
      ∀ z : Point n, z ∈ JensenGlobalContactSet f x0 r delta ->
        HasFDerivWithinAt (fun w : Point n => -G w) (G' z)
          (JensenGlobalContactSet f x0 r delta) z)
    (hdet :
      ∀ z : Point n, z ∈ JensenGlobalContactSet f x0 r delta ->
        ENNReal.ofReal |(G' z).det| <= M) :
    ∃ rho : Real,
      0 < rho ∧
        volume (Metric.ball (0 : Point n) rho) / M <=
          volume (JensenGlobalContactSet f x0 r delta) := by
  exact
    exists_pos_radius_volume_ball_div_le_jensenGlobalContactSet_of_neg_gradient_det_le
      (n := n) (f := f) (x0 := x0) (r := r) (delta := delta) (G := G)
      (G' := G') (M := M)
      hr hdelta hf.continuousOn hf.continuousOn hstrict hderiv
      (measurableSet_jensenGlobalContactSet_of_continuous_gradient
        (n := n) (G := G) hf hG hderiv)
      hM0 hMtop hG' hdet

end ViscositySolns
