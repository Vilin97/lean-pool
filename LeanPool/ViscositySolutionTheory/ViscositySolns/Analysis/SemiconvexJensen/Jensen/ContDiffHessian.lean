/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Analysis.SemiconvexJensen.Jensen.VolumeEstimates

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Jensen Contact-Set Theorem (ContDiffHessian)

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
Derivative of the coordinate gradient map of a `C^2` function.

In quantified mathematical form, if `f : R^n -> R` is twice continuously
differentiable, then the Fréchet derivative at `x` of
`y ↦ linearMapGradient (fderiv Real f y)` is obtained by composing the
second Fréchet derivative of `f` at `x` with the coordinate-gradient map.
-/
theorem hasFDerivAt_coordinate_gradient_fderiv
    {f : Point n -> Real} (hf : ContDiff Real (2 : ℕ∞ω) f) (x : Point n) :
    HasFDerivAt
      (fun y : Point n => linearMapGradient (fderiv Real f y))
      (linearMapGradientCLM (n := n).comp (fderiv Real (fderiv Real f) x)) x := by
  have hfderiv_cd :
      ContDiff Real (1 : ℕ∞ω) (fderiv Real f) := by
    exact hf.fderiv_right (m := (1 : ℕ∞ω)) (by norm_num)
  have hfderiv :
      HasFDerivAt (fderiv Real f) (fderiv Real (fderiv Real f) x) x :=
    (hfderiv_cd.differentiable (by norm_num : (1 : ℕ∞ω) ≠ 0) x).hasFDerivAt
  simpa [Function.comp_def] using
    (linearMapGradientCLM (n := n)).hasFDerivAt.comp x hfderiv

/--
Derivative of the negative coordinate gradient map of a `C^2` function.
-/
theorem hasFDerivAt_neg_coordinate_gradient_fderiv
    {f : Point n -> Real} (hf : ContDiff Real (2 : ℕ∞ω) f) (x : Point n) :
    HasFDerivAt
      (fun y : Point n => -linearMapGradient (fderiv Real f y))
      (-(linearMapGradientCLM (n := n).comp (fderiv Real (fderiv Real f) x))) x := by
  simpa using (hasFDerivAt_coordinate_gradient_fderiv (n := n) hf x).neg

/--
The matrix of the derivative of the coordinate-gradient map is the transpose
of the coordinate Hessian represented by the second Fréchet derivative.
-/
theorem toMatrix_coordinateGradient_comp
    (D2 : Point n →L[Real] Point n →L[Real] Real) :
    LinearMap.toMatrix'
        (((linearMapGradientCLM (n := n)).comp D2 : Point n →L[Real] Point n) :
          Point n →ₗ[Real] Point n) =
      (bilinearMapHessian D2).transpose := by
  ext i j
  have hsingle : Pi.single j (1 : Real) = coordinateVector j := by
    ext k
    by_cases hjk : j = k
    · subst k
      simp [coordinateVector]
    · simp [coordinateVector, hjk]
  simp [LinearMap.toMatrix'_apply, bilinearMapHessian, hsingle]

/--
The absolute determinant of the derivative of the negative coordinate-gradient
map equals the absolute determinant of the coordinate Hessian represented by
the second Fréchet derivative.
-/
theorem abs_det_neg_coordinateGradient_comp
    (D2 : Point n →L[Real] Point n →L[Real] Real) :
    |((-(linearMapGradientCLM (n := n).comp D2) :
        Point n →L[Real] Point n).det)| =
      |(bilinearMapHessian D2).det| := by
  let L : Point n →L[Real] Point n :=
    -(linearMapGradientCLM (n := n).comp D2)
  have hmat :
      LinearMap.toMatrix' ((L : Point n →L[Real] Point n) : Point n →ₗ[Real] Point n) =
        -((bilinearMapHessian D2).transpose) := by
    dsimp [L]
    ext i j
    have hsingle : Pi.single j (1 : Real) = coordinateVector j := by
      ext k
      by_cases hjk : j = k
      · subst k
        simp [coordinateVector]
      · simp [coordinateVector, hjk]
    simp [LinearMap.toMatrix'_apply, bilinearMapHessian, hsingle]
  calc
    |((-(linearMapGradientCLM (n := n).comp D2) :
        Point n →L[Real] Point n).det)| = |LinearMap.det (L : Point n →ₗ[Real] Point n)| := by
          rfl
    _ = |(LinearMap.toMatrix' (L : Point n →ₗ[Real] Point n)).det| := by
          rw [LinearMap.det_toMatrix']
    _ = |(-((bilinearMapHessian D2).transpose)).det| := by
          rw [hmat]
    _ = |(bilinearMapHessian D2).det| := by
          rw [Matrix.det_neg, Matrix.det_transpose]
          simp [abs_mul]

/--
Quantitative Jensen lower bound for the closed-ball global contact set of a
`C^2` function, stated with the determinant bound for the derivative of the
negative gradient map as the remaining pointwise hypothesis.

In quantified mathematical form, assume `f : R^n -> R` is twice continuously
differentiable, `delta > 0`, and every boundary point of `closedBall x0 r`
has strictly smaller `f`-value than `x0`. If the determinant of the derivative
of `z ↦ -Df(z)` is bounded above by `M` on the closed-ball global contact set,
where `M ≠ 0` and `M ≠ ∞`, then there exists `rho > 0` such that
`volume (ball 0 rho) / M ≤ volume (JensenGlobalContactSet f x0 r delta)`.
-/
theorem
    exists_pos_radius_volume_ball_div_le_jensenGlobalContactSet_of_contDiff_two_neg_gradient_det_le
    {f : Point n -> Real} {x0 : Point n} {r delta : Real} {M : ℝ≥0∞}
    (hr : 0 <= r)
    (hdelta : 0 < delta)
    (hf : ContDiff Real (2 : ℕ∞ω) f)
    (hstrict :
      ∀ x : Point n, x ∈ Metric.closedBall x0 r -> dist x x0 = r -> f x < f x0)
    (hM0 : M ≠ 0)
    (hMtop : M ≠ (∞ : ℝ≥0∞))
    (hdet :
      ∀ z : Point n, z ∈ JensenGlobalContactSet f x0 r delta ->
        ENNReal.ofReal
          |(-(linearMapGradientCLM (n := n).comp
              (fderiv Real (fderiv Real f) z))).det| <= M) :
    ∃ rho : Real,
      0 < rho ∧
        volume (Metric.ball (0 : Point n) rho) / M <=
          volume (JensenGlobalContactSet f x0 r delta) := by
  let G : Point n -> Point n :=
    fun z : Point n => linearMapGradient (fderiv Real f z)
  let G' : Point n -> Point n →L[Real] Point n :=
    fun z : Point n =>
      -(linearMapGradientCLM (n := n).comp (fderiv Real (fderiv Real f) z))
  have hfContinuous : Continuous f := hf.continuous
  have hfDifferentiable : Differentiable Real f :=
    hf.differentiable (by norm_num : (2 : ℕ∞ω) ≠ 0)
  have hfFDeriv :
      ContDiff Real (1 : ℕ∞ω) (fderiv Real f) := by
    exact hf.fderiv_right (m := (1 : ℕ∞ω)) (by norm_num)
  have hGContinuous : Continuous G := by
    have hGradient :
        ContDiff Real (1 : ℕ∞ω)
          (fun z : Point n => linearMapGradient (fderiv Real f z)) := by
      simpa [G] using
        hfFDeriv.continuousLinearMap_comp (linearMapGradientCLM (n := n))
    exact hGradient.continuous
  refine
    exists_pos_radius_volume_ball_div_le_jensenGlobalContactSet_of_continuous_gradient_det_le
      (n := n) (f := f) (x0 := x0) (r := r) (delta := delta)
      (G := G) (G' := G') (M := M)
      hr hdelta hfContinuous hGContinuous hstrict ?_ hM0 hMtop ?_ ?_
  · intro z _hz
    simpa [G] using (hfDifferentiable z).hasFDerivAt
  · intro z _hz
    exact (hasFDerivAt_neg_coordinate_gradient_fderiv (n := n) hf z).hasFDerivWithinAt
  · intro z hz
    simpa [G'] using hdet z hz

/--
Quantitative Jensen lower bound for the closed-ball global contact set of a
`C^2` function, stated with the determinant bound for the coordinate Hessian.

In quantified mathematical form, assume `f : R^n -> R` is twice continuously
differentiable, `delta > 0`, and every boundary point of `closedBall x0 r`
has strictly smaller `f`-value than `x0`. If the determinant of the coordinate
Hessian represented by the second Fréchet derivative is bounded above by `M`
on the closed-ball global contact set, where `M ≠ 0` and `M ≠ ∞`, then there
exists `rho > 0` such that
`volume (ball 0 rho) / M ≤ volume (JensenGlobalContactSet f x0 r delta)`.
-/
theorem exists_pos_radius_volume_ball_div_le_jensenGlobalContactSet_of_contDiff_two_hessian_det_le
    {f : Point n -> Real} {x0 : Point n} {r delta : Real} {M : ℝ≥0∞}
    (hr : 0 <= r)
    (hdelta : 0 < delta)
    (hf : ContDiff Real (2 : ℕ∞ω) f)
    (hstrict :
      ∀ x : Point n, x ∈ Metric.closedBall x0 r -> dist x x0 = r -> f x < f x0)
    (hM0 : M ≠ 0)
    (hMtop : M ≠ (∞ : ℝ≥0∞))
    (hdet :
      ∀ z : Point n, z ∈ JensenGlobalContactSet f x0 r delta ->
        ENNReal.ofReal
          |(bilinearMapHessian (fderiv Real (fderiv Real f) z)).det| <= M) :
    ∃ rho : Real,
      0 < rho ∧
        volume (Metric.ball (0 : Point n) rho) / M <=
          volume (JensenGlobalContactSet f x0 r delta) := by
  refine
    exists_pos_radius_volume_ball_div_le_jensenGlobalContactSet_of_contDiff_two_neg_gradient_det_le
      (n := n) (f := f) (x0 := x0) (r := r) (delta := delta) (M := M)
      hr hdelta hf hstrict hM0 hMtop ?_
  intro z hz
  simpa [abs_det_neg_coordinateGradient_comp (n := n)
      (fderiv Real (fderiv Real f) z)] using hdet z hz

/--
A `C^2` function has the ordinary two-sided second-order jet determined by
its first and second Fréchet derivatives.
-/
theorem hasSecondOrderJet_of_contDiff_two
    {f : Point n -> Real} (hf : ContDiff Real (2 : ℕ∞ω) f) (x : Point n) :
    HasSecondOrderJet f x
      (linearMapGradient (fderiv Real f x))
      (bilinearMapHessian (fderiv Real (fderiv Real f) x)) := by
  let J : Jet n :=
    Jet.ofDerivatives (fderiv Real f x) (fderiv Real (fderiv Real f) x)
  have hExpansion : HasSecondOrderExpansionWithin Set.univ f x J := by
    apply hasSecondOrderExpansionWithin_of_contDiffOn_two
    · exact convex_univ
    · exact uniqueDiffOn_univ
    · exact Set.mem_univ x
    · simp
    · exact hf.contDiffOn
    · simp [J]
    · simp [J]
  have hAbove : TouchesAboveOn Set.univ f f x := by
    filter_upwards with y
    simp
  have hBelow : TouchesBelowOn Set.univ f f x := by
    filter_upwards with y
    simp
  have hjet : HasSecondOrderJet f x J.gradient J.hessian :=
    ⟨superjet_of_touchesAbove_hasSecondOrderExpansionWithin hAbove hExpansion,
      subjet_of_touchesBelow_hasSecondOrderExpansionWithin hBelow hExpansion⟩
  exact hjet

/--
At a closed-ball global contact point of a `C^2` function, the coordinate
Hessian is nonpositive.

In quantified mathematical form, if `x` is an interior point of
`closedBall x0 r` where `y ↦ f y + p · y` attains its maximum on the closed
ball, then `D^2 f(x) ≤ 0`.
-/
theorem hessian_le_zero_of_mem_jensenGlobalContactSet_contDiff_two
    {f : Point n -> Real} {x x0 : Point n} {r delta : Real}
    (hf : ContDiff Real (2 : ℕ∞ω) f)
    (hHerm : (bilinearMapHessian (fderiv Real (fderiv Real f) x)).IsHermitian)
    (hx : x ∈ JensenGlobalContactSet f x0 r delta) :
    bilinearMapHessian (fderiv Real (fderiv Real f) x) <= 0 := by
  rcases hx with ⟨hxBall, p, _hp, hmax⟩
  have hlocal : IsLocalMax (linearPerturbation f p) x :=
    hmax.isLocalMax (Metric.closedBall_mem_nhds_of_mem hxBall)
  have hjet :
      HasSecondOrderJet (linearPerturbation f p) x
        (linearMapGradient (fderiv Real f x) + p)
        (bilinearMapHessian (fderiv Real (fderiv Real f) x)) :=
    (hasSecondOrderJet_of_contDiff_two (n := n) hf x).linearPerturbation
  exact hjet.hessian_le_zero_of_isLocalMax hHerm hlocal

/--
The coordinate Hessian of a `C^2` real-valued function is Hermitian.

In quantified mathematical form, if `f : R^n -> R` is twice continuously
differentiable, then for every `x : R^n` and all coordinate vectors `e_i`,
`e_j`, the equality `D^2 f(x)(e_i, e_j) = D^2 f(x)(e_j, e_i)` holds.
-/
theorem contDiff_two_bilinearMapHessian_isHermitian
    {f : Point n -> Real} (hf : ContDiff Real (2 : ℕ∞ω) f) (x : Point n) :
    (bilinearMapHessian (fderiv Real (fderiv Real f) x)).IsHermitian := by
  have hsym : IsSymmSndFDerivAt Real f x :=
    (hf.contDiffAt).isSymmSndFDerivAt (by norm_num)
  apply Matrix.IsHermitian.ext
  intro i j
  change
    (fderiv Real (fderiv Real f) x) (coordinateVector j) (coordinateVector i) =
      (fderiv Real (fderiv Real f) x) (coordinateVector i) (coordinateVector j)
  exact hsym (coordinateVector j) (coordinateVector i)

/--
Convexity of the semiconvex convexification gives the lower Hessian bound for
a `C^2` function.

In quantified mathematical form, if `f : R^n -> R` is twice continuously
differentiable and `x ↦ f x + (lambda / 2) |x|^2` is convex on `R^n`, then
for every `x : R^n`,

`-lambda I ≤ D^2 f(x)`.
-/
theorem hessian_lower_bound_of_convexOn_semiconvexConvexification_contDiff_two
    {f : Point n -> Real} {lambda : Real}
    (hf : ContDiff Real (2 : ℕ∞ω) f)
    (hconv : ConvexOn Real Set.univ (semiconvexConvexification lambda f))
    (x : Point n) :
    -(lambda • (1 : Hessian n)) <=
      bilinearMapHessian (fderiv Real (fderiv Real f) x) := by
  let H : Hessian n := bilinearMapHessian (fderiv Real (fderiv Real f) x)
  let p : Point n := linearMapGradient (fderiv Real f x)
  let A : Jet n := quadraticModelJetAt 0 0 (lambda • (1 : Hessian n)) x
  have hjet : HasSecondOrderJet f x p H := by
    simpa [H, p] using hasSecondOrderJet_of_contDiff_two (n := n) hf x
  have hQ :
      HasSecondOrderExpansionWithin Set.univ
        (fun y : Point n => quadraticModel 0 0 0 (lambda • (1 : Hessian n)) y)
        x A := by
    simpa [A] using
      hasSecondOrderExpansionWithin_quadraticModel_recenter
        (C := Set.univ) (x0 := 0) (r := 0) (p := 0)
        (X := lambda • (1 : Hessian n)) x
  have hsuper :
      ({ gradient := p, hessian := H } : Jet n) + A ∈
        Superjet Set.univ (semiconvexConvexification lambda f) x := by
    have h :=
      superjet_add_hasSecondOrderExpansionWithin
        (C := Set.univ) (u := f)
        (φ := fun y : Point n =>
          quadraticModel 0 0 0 (lambda • (1 : Hessian n)) y)
        (x := x) (J := ({ gradient := p, hessian := H } : Jet n))
        hjet.1 hQ
    exact h
  have hHherm : H.IsHermitian := by
    simpa [H] using contDiff_two_bilinearMapHessian_isHermitian (n := n) hf x
  have hAherm : (lambda • (1 : Hessian n)).IsHermitian :=
    Matrix.isHermitian_one.smul (IsSelfAdjoint.all lambda)
  have hsumHerm :
      ((({ gradient := p, hessian := H } : Jet n) + A).hessian).IsHermitian := by
    exact hHherm.add hAherm
  have hnonneg :
      0 <= ((({ gradient := p, hessian := H } : Jet n) + A).hessian) :=
    Superjet.hessian_nonneg_of_convexOn hconv hsuper hsumHerm
  have hnonneg' : 0 <= H + lambda • (1 : Hessian n) := by
    exact hnonneg
  calc
    -(lambda • (1 : Hessian n)) = 0 - lambda • (1 : Hessian n) := by
      simp
    _ <= (H + lambda • (1 : Hessian n)) - lambda • (1 : Hessian n) :=
      sub_le_sub_right hnonneg' _
    _ = H := by
      abel

/--
Convexity of the semiconvex convexification on a closed ball gives the lower
Hessian bound for a `C^2` function at interior points of that ball.

In quantified mathematical form, if `f : R^n -> R` is twice continuously
differentiable, `x ∈ ball x0 r`, and
`y ↦ f y + (lambda / 2) |y|^2` is convex on `closedBall x0 r`, then

`-lambda I ≤ D^2 f(x)`.
-/
theorem hessian_lower_bound_of_convexOn_closedBall_semiconvexConvexification_contDiff_two
    {f : Point n -> Real} {x x0 : Point n} {r lambda : Real}
    (hf : ContDiff Real (2 : ℕ∞ω) f)
    (hconv : ConvexOn Real (Metric.closedBall x0 r) (semiconvexConvexification lambda f))
    (hx : x ∈ Metric.ball x0 r) :
    -(lambda • (1 : Hessian n)) <=
      bilinearMapHessian (fderiv Real (fderiv Real f) x) := by
  let H : Hessian n := bilinearMapHessian (fderiv Real (fderiv Real f) x)
  let p : Point n := linearMapGradient (fderiv Real f x)
  let A : Jet n := quadraticModelJetAt 0 0 (lambda • (1 : Hessian n)) x
  have hjet : HasSecondOrderJet f x p H := by
    simpa [H, p] using hasSecondOrderJet_of_contDiff_two (n := n) hf x
  have hQ :
      HasSecondOrderExpansionWithin Set.univ
        (fun y : Point n => quadraticModel 0 0 0 (lambda • (1 : Hessian n)) y)
        x A := by
    simpa [A] using
      hasSecondOrderExpansionWithin_quadraticModel_recenter
        (C := Set.univ) (x0 := 0) (r := 0) (p := 0)
        (X := lambda • (1 : Hessian n)) x
  have hsuper :
      ({ gradient := p, hessian := H } : Jet n) + A ∈
        Superjet Set.univ (semiconvexConvexification lambda f) x := by
    have h :=
      superjet_add_hasSecondOrderExpansionWithin
        (C := Set.univ) (u := f)
        (φ := fun y : Point n =>
          quadraticModel 0 0 0 (lambda • (1 : Hessian n)) y)
        (x := x) (J := ({ gradient := p, hessian := H } : Jet n))
        hjet.1 hQ
    exact h
  have hHherm : H.IsHermitian := by
    simpa [H] using contDiff_two_bilinearMapHessian_isHermitian (n := n) hf x
  have hAherm : (lambda • (1 : Hessian n)).IsHermitian :=
    Matrix.isHermitian_one.smul (IsSelfAdjoint.all lambda)
  have hsumHerm :
      ((({ gradient := p, hessian := H } : Jet n) + A).hessian).IsHermitian := by
    exact hHherm.add hAherm
  have hnonneg :
      0 <= ((({ gradient := p, hessian := H } : Jet n) + A).hessian) :=
    Superjet.hessian_nonneg_of_convexOn_closedBall hconv hx hsuper hsumHerm
  have hnonneg' : 0 <= H + lambda • (1 : Hessian n) := by
    exact hnonneg
  calc
    -(lambda • (1 : Hessian n)) = 0 - lambda • (1 : Hessian n) := by
      simp
    _ <= (H + lambda • (1 : Hessian n)) - lambda • (1 : Hessian n) :=
      sub_le_sub_right hnonneg' _
    _ = H := by
      abel

/--
Quantitative Jensen lower bound for the closed-ball global contact set of a
`C^2` function from Hessian order bounds.

In quantified mathematical form, assume `f : R^n -> R` is twice continuously
differentiable, `delta > 0`, and every boundary point of `closedBall x0 r`
has strictly smaller `f`-value than `x0`. Suppose that, at every point of the
closed-ball global contact set, the coordinate Hessian `H z` represented by
the second Fréchet derivative is Hermitian and satisfies
`-lambda I ≤ H z ≤ 0`, with `0 ≤ lambda`. Then there exists `rho > 0` such
that

`volume (ball 0 rho) / ofReal (max (lambda^n) 1)
  ≤ volume (JensenGlobalContactSet f x0 r delta)`.
-/
theorem exists_pos_radius_volume_ball_div_le_jensenGlobalContactSet_of_contDiff_two_hessian_bounds
    {f : Point n -> Real} {x0 : Point n} {r delta lambda : Real}
    (hr : 0 <= r)
    (hdelta : 0 < delta)
    (hf : ContDiff Real (2 : ℕ∞ω) f)
    (hstrict :
      ∀ x : Point n, x ∈ Metric.closedBall x0 r -> dist x x0 = r -> f x < f x0)
    (hlambda : 0 <= lambda)
    (hHerm :
      ∀ z : Point n, z ∈ JensenGlobalContactSet f x0 r delta ->
        (bilinearMapHessian (fderiv Real (fderiv Real f) z)).IsHermitian)
    (hlower :
      ∀ z : Point n, z ∈ JensenGlobalContactSet f x0 r delta ->
        -(lambda • (1 : Hessian n)) <=
          bilinearMapHessian (fderiv Real (fderiv Real f) z))
    (hupper :
      ∀ z : Point n, z ∈ JensenGlobalContactSet f x0 r delta ->
        bilinearMapHessian (fderiv Real (fderiv Real f) z) <= 0) :
    ∃ rho : Real,
      0 < rho ∧
        volume (Metric.ball (0 : Point n) rho) /
            ENNReal.ofReal (max (lambda ^ n) 1) <=
          volume (JensenGlobalContactSet f x0 r delta) := by
  have hM0 : ENNReal.ofReal (max (lambda ^ n) 1) ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (lt_of_lt_of_le zero_lt_one (le_max_right _ _)))
  have hMtop : ENNReal.ofReal (max (lambda ^ n) 1) ≠ (∞ : ℝ≥0∞) :=
    ENNReal.ofReal_ne_top
  refine
    exists_pos_radius_volume_ball_div_le_jensenGlobalContactSet_of_contDiff_two_hessian_det_le
      (n := n) (f := f) (x0 := x0) (r := r) (delta := delta)
      (M := ENNReal.ofReal (max (lambda ^ n) 1))
      hr hdelta hf hstrict hM0 hMtop ?_
  exact ofReal_abs_det_le_of_forall_hessian_bounds
    (n := n) (S := JensenGlobalContactSet f x0 r delta)
    (H := fun z : Point n => bilinearMapHessian (fderiv Real (fderiv Real f) z))
    hlambda hHerm hlower hupper

/--
Quantitative Jensen lower bound for the closed-ball global contact set of a
`C^2` function from the semiconvex lower Hessian bound.

In quantified mathematical form, assume `f : R^n -> R` is twice continuously
differentiable, `delta > 0`, and every boundary point of `closedBall x0 r`
has strictly smaller `f`-value than `x0`. Suppose that, at every point of the
closed-ball global contact set, the coordinate Hessian is Hermitian and
satisfies `-lambda I ≤ D^2 f`, with `0 ≤ lambda`. Then there exists
`rho > 0` such that

`volume (ball 0 rho) / ofReal (max (lambda^n) 1)
  ≤ volume (JensenGlobalContactSet f x0 r delta)`.

The upper Hessian inequality `D^2 f ≤ 0` is supplied by the closed-ball maximum
condition at each interior contact point.
-/
theorem
    exists_pos_radius_volume_ball_div_le_jensenGlobalContactSet_of_contDiff_two_hessian_lower_bound
    {f : Point n -> Real} {x0 : Point n} {r delta lambda : Real}
    (hr : 0 <= r)
    (hdelta : 0 < delta)
    (hf : ContDiff Real (2 : ℕ∞ω) f)
    (hstrict :
      ∀ x : Point n, x ∈ Metric.closedBall x0 r -> dist x x0 = r -> f x < f x0)
    (hlambda : 0 <= lambda)
    (hHerm :
      ∀ z : Point n, z ∈ JensenGlobalContactSet f x0 r delta ->
        (bilinearMapHessian (fderiv Real (fderiv Real f) z)).IsHermitian)
    (hlower :
      ∀ z : Point n, z ∈ JensenGlobalContactSet f x0 r delta ->
        -(lambda • (1 : Hessian n)) <=
          bilinearMapHessian (fderiv Real (fderiv Real f) z)) :
    ∃ rho : Real,
      0 < rho ∧
        volume (Metric.ball (0 : Point n) rho) /
            ENNReal.ofReal (max (lambda ^ n) 1) <=
          volume (JensenGlobalContactSet f x0 r delta) := by
  refine
    exists_pos_radius_volume_ball_div_le_jensenGlobalContactSet_of_contDiff_two_hessian_bounds
      (n := n) (f := f) (x0 := x0) (r := r) (delta := delta)
      (lambda := lambda) hr hdelta hf hstrict hlambda hHerm hlower ?_
  intro z hz
  exact hessian_le_zero_of_mem_jensenGlobalContactSet_contDiff_two
    (n := n) (f := f) (x := z) (x0 := x0) (r := r) (delta := delta)
    hf (hHerm z hz) hz

/--
Quantitative Jensen lower bound for the closed-ball global contact set of a
`C^2` function from a pointwise semiconvex Hessian lower bound.

In quantified mathematical form, assume `f : R^n -> R` is twice continuously
differentiable, `delta > 0`, and every boundary point of `closedBall x0 r`
has strictly smaller `f`-value than `x0`. If `0 ≤ lambda` and
`-lambda I ≤ D^2 f(z)` at every point `z` of the closed-ball global contact
set, then there exists `rho > 0` such that

`volume (ball 0 rho) / ofReal (max (lambda^n) 1)
  ≤ volume (JensenGlobalContactSet f x0 r delta)`.

The Hermitian property of `D^2 f` follows from the symmetry of second
derivatives for `C^2` real-valued functions, and the upper inequality
`D^2 f ≤ 0` follows from the local-maximum second-derivative test.
-/
theorem
    exists_pos_radius_volume_ball_div_le_jensenGlobalContactSet_of_hessian_lower_bound_no_hermitian
    {f : Point n -> Real} {x0 : Point n} {r delta lambda : Real}
    (hr : 0 <= r)
    (hdelta : 0 < delta)
    (hf : ContDiff Real (2 : ℕ∞ω) f)
    (hstrict :
      ∀ x : Point n, x ∈ Metric.closedBall x0 r -> dist x x0 = r -> f x < f x0)
    (hlambda : 0 <= lambda)
    (hlower :
      ∀ z : Point n, z ∈ JensenGlobalContactSet f x0 r delta ->
        -(lambda • (1 : Hessian n)) <=
          bilinearMapHessian (fderiv Real (fderiv Real f) z)) :
    ∃ rho : Real,
      0 < rho ∧
        volume (Metric.ball (0 : Point n) rho) /
            ENNReal.ofReal (max (lambda ^ n) 1) <=
          volume (JensenGlobalContactSet f x0 r delta) := by
  exact
    exists_pos_radius_volume_ball_div_le_jensenGlobalContactSet_of_contDiff_two_hessian_lower_bound
      (n := n) (f := f) (x0 := x0) (r := r) (delta := delta)
      (lambda := lambda) hr hdelta hf hstrict hlambda
      (fun z _hz => contDiff_two_bilinearMapHessian_isHermitian (n := n) hf z)
      hlower

/--
Quantitative Jensen lower bound for the closed-ball global contact set of a
smooth semiconvex function.

In quantified mathematical form, assume `f : R^n -> R` is twice continuously
differentiable, `0 ≤ lambda`, `delta > 0`, every boundary point of
`closedBall x0 r` has strictly smaller `f`-value than `x0`, and
`x ↦ f x + (lambda / 2) |x|^2` is convex on `R^n`. Then there exists
`rho > 0` such that

`volume (ball 0 rho) / ofReal (max (lambda^n) 1)
  ≤ volume (JensenGlobalContactSet f x0 r delta)`.
-/
theorem
    exists_pos_radius_volume_ball_div_le_jensenGlobalContactSet_of_contDiff_two_convexified
    {f : Point n -> Real} {x0 : Point n} {r delta lambda : Real}
    (hr : 0 <= r)
    (hdelta : 0 < delta)
    (hf : ContDiff Real (2 : ℕ∞ω) f)
    (hstrict :
      ∀ x : Point n, x ∈ Metric.closedBall x0 r -> dist x x0 = r -> f x < f x0)
    (hlambda : 0 <= lambda)
    (hconv : ConvexOn Real Set.univ (semiconvexConvexification lambda f)) :
    ∃ rho : Real,
      0 < rho ∧
        volume (Metric.ball (0 : Point n) rho) /
            ENNReal.ofReal (max (lambda ^ n) 1) <=
          volume (JensenGlobalContactSet f x0 r delta) := by
  refine
    exists_pos_radius_volume_ball_div_le_jensenGlobalContactSet_of_hessian_lower_bound_no_hermitian
      (n := n) (f := f) (x0 := x0) (r := r) (delta := delta)
      (lambda := lambda) hr hdelta hf hstrict hlambda ?_
  intro z _hz
  exact hessian_lower_bound_of_convexOn_semiconvexConvexification_contDiff_two
    (n := n) hf hconv z

/--
Quantitative Jensen lower bound for a smooth semiconvex function, with the
boundary-gap radius made explicit.

In quantified mathematical form, assume `f : R^n -> R` is twice continuously
differentiable, `0 ≤ lambda`, `delta > 0`, every boundary point of
`closedBall x0 r` satisfies `f x ≤ f x0 - gamma`, with `gamma > 0`, and
`x ↦ f x + (lambda / 2) |x|^2` is convex on `closedBall x0 r`. Then

`volume (ball 0 rho) / ofReal (max (lambda^n) 1)
  ≤ volume (JensenGlobalContactSet f x0 r delta)`,

where `rho = min (delta / 2) (gamma / (2 * ((n : Real) * r + 1)))`.
-/
theorem volume_explicit_ball_div_le_jensenGlobalContactSet_of_contDiff_two_convexified_boundary_gap
    {f : Point n -> Real} {x0 : Point n} {r delta gamma lambda : Real}
    (hr : 0 <= r)
    (hdelta : 0 < delta)
    (hgamma : 0 < gamma)
    (hf : ContDiff Real (2 : ℕ∞ω) f)
    (hgap :
      ∀ y : Point n, y ∈ Metric.closedBall x0 r -> dist y x0 = r ->
        f y <= f x0 - gamma)
    (hlambda : 0 <= lambda)
    (hconv : ConvexOn Real (Metric.closedBall x0 r) (semiconvexConvexification lambda f)) :
    volume (Metric.ball (0 : Point n)
        (min (delta / 2) (gamma / (2 * ((n : Real) * r + 1))))) /
        ENNReal.ofReal (max (lambda ^ n) 1) <=
      volume (JensenGlobalContactSet f x0 r delta) := by
  let G : Point n -> Point n :=
    fun z : Point n => linearMapGradient (fderiv Real f z)
  let G' : Point n -> Point n →L[Real] Point n :=
    fun z : Point n =>
      -(linearMapGradientCLM (n := n).comp (fderiv Real (fderiv Real f) z))
  have hfContinuous : Continuous f := hf.continuous
  have hfDifferentiable : Differentiable Real f :=
    hf.differentiable (by norm_num : (2 : ℕ∞ω) ≠ 0)
  have hfFDeriv :
      ContDiff Real (1 : ℕ∞ω) (fderiv Real f) := by
    exact hf.fderiv_right (m := (1 : ℕ∞ω)) (by norm_num)
  have hGContinuous : Continuous G := by
    have hGradient :
        ContDiff Real (1 : ℕ∞ω)
          (fun z : Point n => linearMapGradient (fderiv Real f z)) := by
      simpa [G] using
        hfFDeriv.continuousLinearMap_comp (linearMapGradientCLM (n := n))
    exact hGradient.continuous
  have hM0 : ENNReal.ofReal (max (lambda ^ n) 1) ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (lt_of_lt_of_le zero_lt_one (le_max_right _ _)))
  have hMtop : ENNReal.ofReal (max (lambda ^ n) 1) ≠ (∞ : ℝ≥0∞) :=
    ENNReal.ofReal_ne_top
  refine
    volume_explicit_ball_div_le_jensenGlobalContactSet_of_boundary_gap_det_le
      (n := n) (f := f) (x0 := x0) (r := r) (delta := delta)
      (gamma := gamma) (G := G) (G' := G')
      (M := ENNReal.ofReal (max (lambda ^ n) 1))
      hr hdelta hgamma hfContinuous.continuousOn hgap ?_ ?_ hM0 hMtop ?_ ?_
  · intro z _hz
    simpa [G] using (hfDifferentiable z).hasFDerivAt
  · exact measurableSet_jensenGlobalContactSet_of_continuous_gradient
      (n := n) (G := G) hfContinuous hGContinuous
      (by
        intro z _hz
        simpa [G] using (hfDifferentiable z).hasFDerivAt)
  · intro z _hz
    exact (hasFDerivAt_neg_coordinate_gradient_fderiv (n := n) hf z).hasFDerivWithinAt
  · intro z hz
    have hHerm :
        (bilinearMapHessian (fderiv Real (fderiv Real f) z)).IsHermitian :=
      contDiff_two_bilinearMapHessian_isHermitian (n := n) hf z
    have hlower :
        -(lambda • (1 : Hessian n)) <=
          bilinearMapHessian (fderiv Real (fderiv Real f) z) :=
      hessian_lower_bound_of_convexOn_closedBall_semiconvexConvexification_contDiff_two
        (n := n) hf hconv hz.1
    have hupper :
        bilinearMapHessian (fderiv Real (fderiv Real f) z) <= 0 :=
      hessian_le_zero_of_mem_jensenGlobalContactSet_contDiff_two
        (n := n) (f := f) (x := z) (x0 := x0) (r := r) (delta := delta)
        hf hHerm hz
    have hdet :
        ENNReal.ofReal
          |(bilinearMapHessian (fderiv Real (fderiv Real f) z)).det| <=
            ENNReal.ofReal (max (lambda ^ n) 1) :=
      hessian_ofReal_abs_det_le_of_neg_smul_one_le_of_le_zero
        (n := n) (lambda := lambda)
        (A := bilinearMapHessian (fderiv Real (fderiv Real f) z))
        hlambda hHerm hlower hupper
    simpa [G', abs_det_neg_coordinateGradient_comp (n := n)
        (fderiv Real (fderiv Real f) z)] using hdet

/--
Uniformly convergent smooth semiconvex approximants have a common lower
measure bound for their closed-ball global contact sets after discarding
finitely many terms.

In quantified mathematical form, assume every boundary point of
`closedBall x0 r` satisfies `f x ≤ f x0 - gamma`, with `gamma > 0`, and assume
`f_m -> f` uniformly on `closedBall x0 r`. Suppose also that every `f_m` is
twice continuously differentiable and that
`x ↦ f_m x + (lambda / 2) |x|^2` is convex on `closedBall x0 r`, with the same
`lambda ≥ 0` for all `m`. Then there are a natural number `N` and a number
`c > 0` such that, for every `m ≥ N`,

* `JensenGlobalContactSet f_m x0 r delta` is measurable;
* `c ≤ volume (JensenGlobalContactSet f_m x0 r delta)`.
-/
theorem
    exists_tail_measurable_common_lower_bound_jensenGlobalContactSet_of_uniformOn_convexified
    {f : Point n -> Real} {fseq : Nat -> Point n -> Real}
    {x0 : Point n} {r delta gamma lambda : Real}
    (hr : 0 <= r)
    (hdelta : 0 < delta)
    (hgamma : 0 < gamma)
    (hgap :
      ∀ x : Point n, x ∈ Metric.closedBall x0 r -> dist x x0 = r ->
        f x <= f x0 - gamma)
    (hunif :
      ∀ eps : Real, 0 < eps ->
        ∃ N : Nat, ∀ m : Nat, N <= m ->
          ∀ z : Point n, z ∈ Metric.closedBall x0 r ->
            |fseq m z - f z| <= eps)
    (hfseq : ∀ m : Nat, ContDiff Real (2 : ℕ∞ω) (fseq m))
    (hlambda : 0 <= lambda)
    (hconvseq :
      ∀ m : Nat,
        ConvexOn Real (Metric.closedBall x0 r) (semiconvexConvexification lambda (fseq m))) :
    ∃ N : Nat,
    ∃ c : ℝ≥0∞,
      0 < c ∧
        (∀ m : Nat, N <= m ->
          MeasurableSet (JensenGlobalContactSet (fseq m) x0 r delta)) ∧
        (∀ m : Nat, N <= m ->
          c <= volume (JensenGlobalContactSet (fseq m) x0 r delta)) := by
  rcases eventually_boundary_gap_of_uniformOn_closedBall
      (n := n) (f := f) (fseq := fseq) (x0 := x0) (r := r)
      (gamma := gamma)
      hr hgamma hgap hunif with
    ⟨N, hgap_tail⟩
  let rho : Real :=
    min (delta / 2) ((gamma / 2) / (2 * ((n : Real) * r + 1)))
  let M : ℝ≥0∞ := ENNReal.ofReal (max (lambda ^ n) 1)
  let c : ℝ≥0∞ := volume (Metric.ball (0 : Point n) rho) / M
  have hgamma_half : 0 < gamma / 2 := by linarith
  have ha_nonneg : 0 <= (n : Real) * r := by
    exact mul_nonneg (Nat.cast_nonneg n) hr
  have ha1_pos : 0 < (n : Real) * r + 1 := by
    linarith
  have hden_pos : 0 < 2 * ((n : Real) * r + 1) := by positivity
  have hrho_pos : 0 < rho := by
    dsimp [rho]
    exact lt_min (half_pos hdelta) (div_pos hgamma_half hden_pos)
  have hMtop : M ≠ (∞ : ℝ≥0∞) := by
    dsimp [M]
    exact ENNReal.ofReal_ne_top
  have hcpos : 0 < c := by
    have hball_pos : 0 < volume (Metric.ball (0 : Point n) rho) :=
      Metric.measure_ball_pos volume (0 : Point n) hrho_pos
    exact ENNReal.div_pos hball_pos.ne' hMtop
  refine ⟨N, c, hcpos, ?_, ?_⟩
  · intro m _hm
    let G : Point n -> Point n :=
      fun z : Point n => linearMapGradient (fderiv Real (fseq m) z)
    have hfContinuous : Continuous (fseq m) := (hfseq m).continuous
    have hfDifferentiable : Differentiable Real (fseq m) :=
      (hfseq m).differentiable (by norm_num : (2 : ℕ∞ω) ≠ 0)
    have hfFDeriv :
        ContDiff Real (1 : ℕ∞ω) (fderiv Real (fseq m)) := by
      exact (hfseq m).fderiv_right (m := (1 : ℕ∞ω)) (by norm_num)
    have hGContinuous : Continuous G := by
      have hGradient :
          ContDiff Real (1 : ℕ∞ω)
            (fun z : Point n => linearMapGradient (fderiv Real (fseq m) z)) := by
        simpa [G] using
          hfFDeriv.continuousLinearMap_comp (linearMapGradientCLM (n := n))
      exact hGradient.continuous
    exact measurableSet_jensenGlobalContactSet_of_continuous_gradient
      (n := n) (G := G) hfContinuous hGContinuous
      (by
        intro z _hz
        simpa [G] using (hfDifferentiable z).hasFDerivAt)
  · intro m hm
    exact
      volume_explicit_ball_div_le_jensenGlobalContactSet_of_contDiff_two_convexified_boundary_gap
        (n := n) (f := fseq m) (x0 := x0) (r := r) (delta := delta)
        (gamma := gamma / 2) (lambda := lambda)
        hr hdelta hgamma_half (hfseq m) (hgap_tail m hm) hlambda (hconvseq m)

/--
Positive measure of the Jensen contact set for a globally `C^2` function.

In quantified mathematical form, if `f : R^n -> R` is twice continuously
differentiable, if `delta > 0`, and if every point of `closedBall x0 r` whose
distance from `x0` is exactly `r` has strictly smaller `f`-value than `x0`,
then `JensenContactSet f x0 r delta` has positive Lebesgue measure.
-/
theorem volume_pos_jensenContactSet_of_contDiff_two
    {f : Point n -> Real} {x0 : Point n} {r delta : Real}
    (hr : 0 <= r)
    (hdelta : 0 < delta)
    (hf : ContDiff Real (2 : ℕ∞ω) f)
    (hstrict :
      ∀ x : Point n, x ∈ Metric.closedBall x0 r -> dist x x0 = r -> f x < f x0) :
    0 < volume (JensenContactSet f x0 r delta) := by
  have hfContinuous : Continuous f := hf.continuous
  have hfDifferentiable : Differentiable Real f :=
    hf.differentiable (by norm_num : (2 : ℕ∞ω) ≠ 0)
  have hfFDeriv :
      ContDiff Real (1 : ℕ∞ω) (fderiv Real f) := by
    exact hf.fderiv_right (m := (1 : ℕ∞ω)) (by norm_num)
  have hGradient :
      ContDiff Real (1 : ℕ∞ω)
        (fun z : Point n => linearMapGradient (fderiv Real f z)) := by
    simpa using
      hfFDeriv.continuousLinearMap_comp (linearMapGradientCLM (n := n))
  have hNegGradient :
      Differentiable Real
        (fun z : Point n => -linearMapGradient (fderiv Real f z)) := by
    exact hGradient.neg.differentiable (by norm_num : (1 : ℕ∞ω) ≠ 0)
  refine volume_pos_jensenContactSet_of_differentiableOn_neg_gradient
    (n := n) (f := f) (x0 := x0) (r := r) (delta := delta)
    (G := fun z : Point n => linearMapGradient (fderiv Real f z))
    hr hdelta hfContinuous.continuousOn hfContinuous.continuousOn hstrict ?_ ?_
  · intro z _hz
    simpa using (hfDifferentiable z).hasFDerivAt
  · exact hNegGradient.differentiableOn

/--
Positive measure of the Jensen contact set for a globally `C^2` function,
using the strict maximum hypothesis on the whole closed ball.

In quantified mathematical form, if `r > 0`, `delta > 0`, `f : R^n -> R` is
twice continuously differentiable, and `f x < f x0` for every
`x ∈ closedBall x0 r` with `x ≠ x0`, then
`JensenContactSet f x0 r delta` has positive Lebesgue measure.
-/
theorem volume_pos_jensenContactSet_of_contDiff_two_closedBall_strict
    {f : Point n -> Real} {x0 : Point n} {r delta : Real}
    (hr : 0 < r)
    (hdelta : 0 < delta)
    (hf : ContDiff Real (2 : ℕ∞ω) f)
    (hstrict :
      ∀ x : Point n, x ∈ Metric.closedBall x0 r -> x ≠ x0 -> f x < f x0) :
    0 < volume (JensenContactSet f x0 r delta) := by
  refine volume_pos_jensenContactSet_of_contDiff_two
    (n := n) (f := f) (x0 := x0) (r := r) (delta := delta)
    hr.le hdelta hf ?_
  intro x hx hdist
  exact hstrict x hx (fun hx0 => by
    subst x
    simp [dist_self] at hdist
    linarith)

end ViscositySolns
