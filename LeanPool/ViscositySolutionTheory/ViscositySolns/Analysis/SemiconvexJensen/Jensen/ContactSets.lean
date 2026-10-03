/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Complex.Tietze
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Analysis.SemiconvexJensen.Aleksandrov.JetCalculus.Convex
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Analysis.SemiconvexJensen.Aleksandrov.JetCalculus.Determinant
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Analysis.SemiconvexJensen.Strictification

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Jensen Contact-Set Theorem (ContactSets)

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
The contact set appearing in Jensen's lemma.

In quantified mathematical form, `JensenContactSet f x0 r delta` is the set of
points `x` in the closed ball `B(x0, r)` for which there exists
`p ∈ B(0, delta)` such that `y ↦ f y + p · y` has a local maximum at `x`.
-/
def JensenContactSet (f : Point n -> Real) (x0 : Point n) (r delta : Real) :
    Set (Point n) :=
  {x | x ∈ Metric.closedBall x0 r ∧
    ∃ p : Point n, p ∈ Metric.ball 0 delta ∧ IsLocalMax (linearPerturbation f p) x}

/--
The closed-ball global contact set appearing before the passage to local
contacts in the proof of Jensen's lemma.

In quantified mathematical form, `JensenGlobalContactSet f x0 r delta` is the
set of points `x` in the open ball `B(x0, r)` for which there exists
`p ∈ B(0, delta)` such that `x` is a maximum point of
`y ↦ f y + p · y` on the closed ball `closedBall x0 r`.
-/
def JensenGlobalContactSet (f : Point n -> Real) (x0 : Point n) (r delta : Real) :
    Set (Point n) :=
  {x | x ∈ Metric.ball x0 r ∧
    ∃ p : Point n, p ∈ Metric.ball 0 delta ∧
      IsMaxOn (linearPerturbation f p) (Metric.closedBall x0 r) x}

/--
The closed-ball global contact set parametrized by the gradient.

In quantified mathematical form, `JensenGradientGlobalContactSet f G x0 r δ`
is the set of all `x ∈ ball x0 r` such that `-G x ∈ ball 0 δ` and `x`
maximizes `y ↦ f y - G x · y` on `closedBall x0 r`.
-/
def JensenGradientGlobalContactSet
    (f : Point n -> Real) (G : Point n -> Point n) (x0 : Point n)
    (r delta : Real) : Set (Point n) :=
  {x | x ∈ Metric.ball x0 r ∧
    -G x ∈ Metric.ball 0 delta ∧
      ∀ y : Point n, y ∈ Metric.closedBall x0 r ->
        linearPerturbation f (-G x) y <= linearPerturbation f (-G x) x}

/--
The gradient-parametrized global contact set is measurable when both the
function and the gradient are continuous.
-/
theorem measurableSet_jensenGradientGlobalContactSet
    {f : Point n -> Real} {G : Point n -> Point n} {x0 : Point n}
    {r delta : Real}
    (hf : Continuous f) (hG : Continuous G) :
    MeasurableSet (JensenGradientGlobalContactSet f G x0 r delta) := by
  have hball :
      MeasurableSet {x : Point n | x ∈ Metric.ball x0 r} :=
    Metric.isOpen_ball.measurableSet
  have hgradBall :
      MeasurableSet {x : Point n | -G x ∈ Metric.ball (0 : Point n) delta} :=
    (Metric.isOpen_ball.preimage hG.neg).measurableSet
  have hmaxSet :
      MeasurableSet
        {x : Point n |
          ∀ y : Point n, y ∈ Metric.closedBall x0 r ->
            linearPerturbation f (-G x) y <= linearPerturbation f (-G x) x} := by
    let K : Set (Point n) := Metric.closedBall x0 r
    let E : Set (Point n) :=
      ⋂ y : Point n, ⋂ (_hy : y ∈ K),
        {x : Point n |
          linearPerturbation f (-G x) y <= linearPerturbation f (-G x) x}
    have hEclosed : IsClosed E := by
      dsimp [E]
      refine isClosed_iInter ?_
      intro y
      refine isClosed_iInter ?_
      intro _hy
      have hleft :
          Continuous fun x : Point n => linearPerturbation f (-G x) y := by
        dsimp [linearPerturbation]
        exact continuous_const.add (hG.neg.dotProduct continuous_const)
      have hright :
          Continuous fun x : Point n => linearPerturbation f (-G x) x := by
        dsimp [linearPerturbation]
        exact hf.add (hG.neg.dotProduct continuous_id)
      exact isClosed_le hleft hright
    have hset :
        {x : Point n |
          ∀ y : Point n, y ∈ Metric.closedBall x0 r ->
            linearPerturbation f (-G x) y <= linearPerturbation f (-G x) x} = E := by
      ext x
      simp [E, K]
    rw [hset]
    exact hEclosed.measurableSet
  simpa [JensenGradientGlobalContactSet, Set.ofPred_and] using
    (hball.inter (hgradBall.inter hmaxSet))

/--
For a differentiable function, the closed-ball global contact set is the same
as the gradient-parametrized global contact set.

In quantified mathematical form, if `Df(x) = G x` for every `x ∈ ball x0 r`,
then an interior maximizer of `y ↦ f y + p · y` on `closedBall x0 r` satisfies
`p = -G x`. Consequently the existential perturbation in
`JensenGlobalContactSet` may be replaced by the single perturbation `-G x`.
-/
theorem JensenGlobalContactSet_eq_jensenGradientGlobalContactSet
    {f : Point n -> Real} {G : Point n -> Point n} {x0 : Point n}
    {r delta : Real}
    (hderiv :
      ∀ z : Point n, z ∈ Metric.ball x0 r ->
        HasFDerivAt f (gradientLinearMap (G z)) z) :
    JensenGlobalContactSet f x0 r delta =
      JensenGradientGlobalContactSet f G x0 r delta := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxBall, p, hpDelta, hmax⟩
    have hlocal : IsLocalMax (linearPerturbation f p) x :=
      hmax.isLocalMax (Metric.closedBall_mem_nhds_of_mem hxBall)
    have hgrad :
        G x + p = 0 :=
      gradient_add_eq_zero_of_isLocalMax_linearPerturbation_hasFDerivAt
        (n := n) hlocal (hderiv x hxBall)
    have hp_eq : -G x = p := by
      rw [neg_eq_iff_add_eq_zero]
      simpa [add_comm] using hgrad
    refine ⟨hxBall, ?_, ?_⟩
    · simpa [hp_eq] using hpDelta
    · intro y hy
      simpa [hp_eq] using hmax hy
  · intro hx
    rcases hx with ⟨hxBall, hpDelta, hmax⟩
    refine ⟨hxBall, -G x, hpDelta, ?_⟩
    intro y hy
    exact hmax y hy

/--
The closed-ball global contact set is measurable for a differentiable function
with continuous gradient.
-/
theorem measurableSet_jensenGlobalContactSet_of_continuous_gradient
    {f : Point n -> Real} {G : Point n -> Point n} {x0 : Point n}
    {r delta : Real}
    (hf : Continuous f) (hG : Continuous G)
    (hderiv :
      ∀ z : Point n, z ∈ Metric.ball x0 r ->
        HasFDerivAt f (gradientLinearMap (G z)) z) :
    MeasurableSet (JensenGlobalContactSet f x0 r delta) := by
  rw [JensenGlobalContactSet_eq_jensenGradientGlobalContactSet
    (n := n) (G := G) hderiv]
  exact measurableSet_jensenGradientGlobalContactSet (n := n) hf hG

/--
The closed-ball global contact set is contained in the open ball appearing in
its definition.
-/
theorem JensenGlobalContactSet.subset_ball
    (f : Point n -> Real) (x0 : Point n) (r delta : Real) :
    JensenGlobalContactSet f x0 r delta ⊆ Metric.ball x0 r := by
  intro x hx
  exact hx.1

/--
The closed-ball global contact set is contained in the closed ball with the
same center and radius.
-/
theorem JensenGlobalContactSet.subset_closedBall
    (f : Point n -> Real) (x0 : Point n) (r delta : Real) :
    JensenGlobalContactSet f x0 r delta ⊆ Metric.closedBall x0 r := by
  intro x hx
  exact Metric.ball_subset_closedBall hx.1

/--
The contact set is contained in the closed ball appearing in its definition.
-/
theorem JensenContactSet.subset_closedBall
    (f : Point n -> Real) (x0 : Point n) (r delta : Real) :
    JensenContactSet f x0 r delta ⊆ Metric.closedBall x0 r := by
  intro x hx
  exact hx.1

/--
The contact set is monotone in the radius of the closed ball.

In quantified mathematical form, if `r₁ ≤ r₂`, then every contact point in
`closedBall x0 r₁` is also a contact point in `closedBall x0 r₂`, with the
same perturbing vector.
-/
theorem JensenContactSet.mono_radius
    {f : Point n -> Real} {x0 : Point n} {r₁ r₂ delta : Real} (hr : r₁ <= r₂) :
    JensenContactSet f x0 r₁ delta ⊆ JensenContactSet f x0 r₂ delta := by
  intro x hx
  rcases hx with ⟨hxBall, p, hp, hmax⟩
  exact ⟨Metric.closedBall_subset_closedBall hr hxBall, p, hp, hmax⟩

/--
Positive measure of the contact set is preserved when the radius is enlarged.

In quantified mathematical form, if `r₁ ≤ r₂` and
`JensenContactSet f x0 r₁ δ` has positive Lebesgue measure, then
`JensenContactSet f x0 r₂ δ` also has positive Lebesgue measure.
-/
theorem JensenContactSet.measure_pos_of_mono_radius
    {f : Point n -> Real} {x0 : Point n} {r₁ r₂ delta : Real} (hr : r₁ <= r₂)
    (hpos : 0 < volume (JensenContactSet f x0 r₁ delta)) :
    0 < volume (JensenContactSet f x0 r₂ delta) :=
  lt_of_lt_of_le hpos (measure_mono (JensenContactSet.mono_radius hr))

/--
The contact set is monotone in the allowed size of the perturbing vector.

In quantified mathematical form, if `δ₁ ≤ δ₂`, then every point obtained using
a perturbing vector `p ∈ ball 0 δ₁` is also obtained using a perturbing
vector `p ∈ ball 0 δ₂`.
-/
theorem JensenContactSet.mono_delta
    {f : Point n -> Real} {x0 : Point n} {r delta₁ delta₂ : Real}
    (hdelta : delta₁ <= delta₂) :
    JensenContactSet f x0 r delta₁ ⊆ JensenContactSet f x0 r delta₂ := by
  intro x hx
  rcases hx with ⟨hxBall, p, hp, hmax⟩
  exact ⟨hxBall, p, Metric.ball_subset_ball hdelta hp, hmax⟩

/--
Positive measure of the contact set is preserved when the allowed perturbing
vectors are enlarged.

In quantified mathematical form, if `δ₁ ≤ δ₂` and
`JensenContactSet f x0 r δ₁` has positive Lebesgue measure, then
`JensenContactSet f x0 r δ₂` also has positive Lebesgue measure.
-/
theorem JensenContactSet.measure_pos_of_mono_delta
    {f : Point n -> Real} {x0 : Point n} {r delta₁ delta₂ : Real}
    (hdelta : delta₁ <= delta₂)
    (hpos : 0 < volume (JensenContactSet f x0 r delta₁)) :
    0 < volume (JensenContactSet f x0 r delta₂) :=
  lt_of_lt_of_le hpos (measure_mono (JensenContactSet.mono_delta hdelta))

/--
The strict maximum point belongs to the contact set for the zero perturbation.

In quantified mathematical form, if `0 ≤ r`, `0 < δ`, and `x0` is a strict
local maximum point of `f`, then `x0 ∈ JensenContactSet f x0 r δ`.
-/
theorem StrictLocalMax.mem_jensenContactSet
    {f : Point n -> Real} {x0 : Point n} {r delta : Real}
    (h : StrictLocalMax f x0) (hr : 0 <= r) (hdelta : 0 < delta) :
    x0 ∈ JensenContactSet f x0 r delta := by
  refine ⟨Metric.mem_closedBall_self hr, 0, ?_, ?_⟩
  · simpa using hdelta
  · filter_upwards [h.isLocalMax] with x hx
    simpa [linearPerturbation, dotProduct] using hx

/--
The linear part of a perturbation is uniformly bounded on a closed ball.

In quantified mathematical form, if `x ∈ closedBall x0 r`, then

`|p · x - p · x0| ≤ n ‖p‖ r`,

where `n` is the dimension of `R^n` and the norm is the finite product norm
used by Lean on `Fin n -> Real`.
-/
theorem abs_dotProduct_sub_dotProduct_center_le_of_mem_closedBall
    {x x0 p : Point n} {r : Real} (hx : x ∈ Metric.closedBall x0 r) :
    |dotProduct p x - dotProduct p x0| <= (n : Real) * ‖p‖ * r := by
  have hdist : ‖x - x0‖ <= r := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  have hdot :
      |dotProduct p (x - x0)| <= (n : Real) * ‖p‖ * ‖x - x0‖ :=
    abs_dotProduct_le_card_mul_norm_mul_norm p (x - x0)
  have hcoeff_nonneg : 0 <= (n : Real) * ‖p‖ := by
    positivity
  have hmul :
      (n : Real) * ‖p‖ * ‖x - x0‖ <= (n : Real) * ‖p‖ * r := by
    exact mul_le_mul_of_nonneg_left hdist hcoeff_nonneg
  have hdiff :
      dotProduct p x - dotProduct p x0 = dotProduct p (x - x0) := by
    simp [dotProduct_sub]
  rw [hdiff]
  exact hdot.trans hmul

/--
Small linear perturbations remain below the center on the boundary of a closed
ball when the unperturbed function has a positive boundary gap.

In quantified mathematical form, suppose that every `x ∈ closedBall x0 r`
with `dist x x0 = r` satisfies `f x ≤ f x0 - gamma`, and suppose
`n ‖p‖ r < gamma`. Then every such boundary point satisfies
`f x + p · x < f x0 + p · x0`.
-/
theorem linearPerturbation_lt_center_of_boundary_gap
    {f : Point n -> Real} {x x0 p : Point n} {r gamma : Real}
    (hx : x ∈ Metric.closedBall x0 r) (hboundary : dist x x0 = r)
    (hgap :
      ∀ y : Point n, y ∈ Metric.closedBall x0 r -> dist y x0 = r ->
        f y <= f x0 - gamma)
    (hp : (n : Real) * ‖p‖ * r < gamma) :
    linearPerturbation f p x < linearPerturbation f p x0 := by
  have hlin_abs :=
    abs_dotProduct_sub_dotProduct_center_le_of_mem_closedBall (n := n) (p := p) hx
  have hlin_le : dotProduct p x - dotProduct p x0 <= (n : Real) * ‖p‖ * r :=
    le_trans (le_abs_self _) hlin_abs
  have hf_gap := hgap x hx hboundary
  dsimp [linearPerturbation]
  linarith

/--
A maximum point of a sufficiently small linear perturbation on a closed ball
is not on the boundary.

In quantified mathematical form, assume `0 ≤ r`, every boundary point `x` of
`closedBall x0 r` satisfies `f x ≤ f x0 - gamma`, and
`n ‖p‖ r < gamma`. If `z` maximizes `y ↦ f y + p · y` on
`closedBall x0 r`, then `dist z x0 < r`.
-/
theorem isMaxOn_linearPerturbation_closedBall_mem_ball_of_boundary_gap
    {f : Point n -> Real} {z x0 p : Point n} {r gamma : Real}
    (hr : 0 <= r)
    (hgap :
      ∀ y : Point n, y ∈ Metric.closedBall x0 r -> dist y x0 = r ->
        f y <= f x0 - gamma)
    (hp : (n : Real) * ‖p‖ * r < gamma)
    (hz : z ∈ Metric.closedBall x0 r)
    (hmax : IsMaxOn (linearPerturbation f p) (Metric.closedBall x0 r) z) :
    z ∈ Metric.ball x0 r := by
  rw [Metric.mem_ball]
  have hzdist : dist z x0 <= r := by
    simpa [Metric.mem_closedBall] using hz
  by_contra hnot
  have hboundary : dist z x0 = r := le_antisymm hzdist (le_of_not_gt hnot)
  have hcenter : x0 ∈ Metric.closedBall x0 r := Metric.mem_closedBall_self hr
  have hle_center : linearPerturbation f p x0 <= linearPerturbation f p z := hmax hcenter
  have hlt_center :=
    linearPerturbation_lt_center_of_boundary_gap
      (n := n) (f := f) (x := z) (x0 := x0) (p := p)
      hz hboundary hgap hp
  exact (not_lt_of_ge hle_center) hlt_center

/--
Continuity and strict boundary inequality give a positive boundary gap.

In quantified mathematical form, suppose `f` is continuous on
`sphere x0 r`, and suppose that every point `x ∈ closedBall x0 r` with
`dist x x0 = r` satisfies `f x < f x0`. Then there exists `gamma > 0` such
that every such boundary point satisfies `f x ≤ f x0 - gamma`.
-/
theorem exists_pos_boundary_gap_of_continuousOn_sphere
    {f : Point n -> Real} {x0 : Point n} {r : Real}
    (hf : ContinuousOn f (Metric.sphere x0 r))
    (hstrict :
      ∀ x : Point n, x ∈ Metric.closedBall x0 r -> dist x x0 = r -> f x < f x0) :
    ∃ gamma : Real, 0 < gamma ∧
      ∀ x : Point n, x ∈ Metric.closedBall x0 r -> dist x x0 = r ->
        f x <= f x0 - gamma := by
  by_cases hne : (Metric.sphere x0 r).Nonempty
  · rcases (isCompact_sphere x0 r).exists_isMaxOn hne hf with ⟨z, hzSphere, hmax⟩
    have hzClosed : z ∈ Metric.closedBall x0 r := by
      exact Metric.sphere_subset_closedBall hzSphere
    have hzBoundary : dist z x0 = r := by
      simpa [dist_eq_norm] using hzSphere
    have hzlt : f z < f x0 := hstrict z hzClosed hzBoundary
    refine ⟨(f x0 - f z) / 2, by linarith, ?_⟩
    intro x hxClosed hxBoundary
    have hxSphere : x ∈ Metric.sphere x0 r := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hxBoundary
    have hle_z : f x <= f z := hmax hxSphere
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro x _hxClosed hxBoundary
    have hxSphere : x ∈ Metric.sphere x0 r := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hxBoundary
    exact False.elim (hne ⟨x, hxSphere⟩)

/--
Semiconvexity on a larger closed ball and strict boundary inequality on a
smaller closed ball give a positive boundary gap.

In quantified mathematical form, suppose `r < R`, `f : R^n -> R` satisfies
the coordinate semiconvexity inequality on `closedBall x0 R`, and every
`x ∈ closedBall x0 r` with `dist x x0 = r` satisfies `f x < f x0`. Then
there exists `gamma > 0` such that every such boundary point satisfies
`f x ≤ f x0 - gamma`.
-/
theorem exists_pos_boundary_gap_of_coordinateSemiconvexOn_larger_closedBall
    {f : Point n -> Real} {x0 : Point n} {r R lambda : Real}
    (hsemi : CoordinateSemiconvexOn lambda (Metric.closedBall x0 R) f)
    (hrR : r < R)
    (hstrict :
      ∀ x : Point n, x ∈ Metric.closedBall x0 r -> dist x x0 = r -> f x < f x0) :
    ∃ gamma : Real, 0 < gamma ∧
      ∀ x : Point n, x ∈ Metric.closedBall x0 r -> dist x x0 = r ->
        f x <= f x0 - gamma :=
  exists_pos_boundary_gap_of_continuousOn_sphere
    (n := n) (f := f) (x0 := x0) (r := r)
    (CoordinateSemiconvexOn.continuousOn_sphere_of_closedBall hsemi hrR) hstrict

/--
The boundary-exclusion theorem with the positive boundary gap supplied by
continuity and strict boundary inequality.

In quantified mathematical form, suppose `f` is continuous on `sphere x0 r`
and `f x < f x0` for every boundary point of `closedBall x0 r`. Then there
exists `gamma > 0` such that every perturbing vector `p` satisfying
`n ‖p‖ r < gamma` has the following property: every maximum of
`x ↦ f x + p · x` on `closedBall x0 r` lies in `ball x0 r`.
-/
theorem exists_pos_boundary_gap_eventually_isMaxOn_mem_ball
    {f : Point n -> Real} {x0 : Point n} {r : Real}
    (hr : 0 <= r)
    (hf : ContinuousOn f (Metric.sphere x0 r))
    (hstrict :
      ∀ x : Point n, x ∈ Metric.closedBall x0 r -> dist x x0 = r -> f x < f x0) :
    ∃ gamma : Real, 0 < gamma ∧
      ∀ p z : Point n,
        (n : Real) * ‖p‖ * r < gamma ->
          z ∈ Metric.closedBall x0 r ->
            IsMaxOn (linearPerturbation f p) (Metric.closedBall x0 r) z ->
              z ∈ Metric.ball x0 r := by
  rcases exists_pos_boundary_gap_of_continuousOn_sphere
      (n := n) (f := f) (x0 := x0) (r := r) hf hstrict with
    ⟨gamma, hgamma_pos, hgap⟩
  exact ⟨gamma, hgamma_pos, fun p z hp hz hmax =>
    isMaxOn_linearPerturbation_closedBall_mem_ball_of_boundary_gap
      (n := n) (f := f) (z := z) (x0 := x0) (p := p)
      hr hgap hp hz hmax⟩

/--
An interior maximum on the closed ball gives a point of Jensen's contact set.

In quantified mathematical form, if `z` maximizes `y ↦ f y + p · y` on
`closedBall x0 r`, if `z ∈ ball x0 r`, and if `p ∈ ball 0 δ`, then
`z ∈ JensenContactSet f x0 r δ`.
-/
theorem mem_jensenContactSet_of_isMaxOn_closedBall_of_mem_ball
    {f : Point n -> Real} {z x0 p : Point n} {r delta : Real}
    (hzClosed : z ∈ Metric.closedBall x0 r)
    (hzBall : z ∈ Metric.ball x0 r)
    (hpDelta : p ∈ Metric.ball (0 : Point n) delta)
    (hmax : IsMaxOn (linearPerturbation f p) (Metric.closedBall x0 r) z) :
    z ∈ JensenContactSet f x0 r delta := by
  refine ⟨hzClosed, p, hpDelta, ?_⟩
  exact hmax.isLocalMax (Metric.closedBall_mem_nhds_of_mem hzBall)

/--
Every closed-ball global contact point is a Jensen contact point.

In quantified mathematical form, if `x ∈ B(x0, r)` and there exists
`p ∈ B(0, delta)` such that `x` maximizes `y ↦ f y + p · y` on
`closedBall x0 r`, then `x ∈ JensenContactSet f x0 r delta`.
-/
theorem JensenGlobalContactSet.subset_jensenContactSet
    (f : Point n -> Real) (x0 : Point n) (r delta : Real) :
    JensenGlobalContactSet f x0 r delta ⊆ JensenContactSet f x0 r delta := by
  intro x hx
  rcases hx with ⟨hxBall, p, hpDelta, hmax⟩
  exact mem_jensenContactSet_of_isMaxOn_closedBall_of_mem_ball
    (n := n) (f := f) (z := x) (x0 := x0) (p := p)
    (Metric.ball_subset_closedBall hxBall) hxBall hpDelta hmax

/--
Uniform convergence on a closed ball gives convergence at each point of that
closed ball after passing to any sequence of indices tending to infinity.

In quantified mathematical form, assume that for every `ε > 0` there exists
`N` such that, for every `m ≥ N` and every `y ∈ closedBall x0 r`,
`|f_m(y) - f(y)| ≤ ε`. If `i_j -> ∞` and `y ∈ closedBall x0 r`, then
`f_{i_j}(y) -> f(y)`.
-/
theorem tendsto_eval_of_uniformOn_closedBall_comp
    {fseq : Nat -> Point n -> Real} {f : Point n -> Real}
    {x0 y : Point n} {r : Real} {idx : Nat -> Nat}
    (hunif :
      ∀ eps : Real, 0 < eps ->
        ∃ N : Nat, ∀ m : Nat, N <= m ->
          ∀ z : Point n, z ∈ Metric.closedBall x0 r ->
            |fseq m z - f z| <= eps)
    (hidx : Filter.Tendsto idx Filter.atTop Filter.atTop)
    (hy : y ∈ Metric.closedBall x0 r) :
    Filter.Tendsto (fun j : Nat => fseq (idx j) y) Filter.atTop (𝓝 (f y)) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  rcases hunif (eps / 2) (half_pos heps) with ⟨N, hN⟩
  have hevent : ∀ᶠ j in Filter.atTop, N <= idx j :=
    hidx (Filter.eventually_ge_atTop N)
  rcases (Filter.eventually_atTop.1 hevent) with ⟨J, hJ⟩
  refine ⟨J, ?_⟩
  intro j hj
  have hclose := hN (idx j) (hJ j hj) y hy
  have hdist : dist (fseq (idx j) y) (f y) = |fseq (idx j) y - f y| := by
    rw [Real.dist_eq]
  rw [hdist]
  exact lt_of_le_of_lt hclose (by linarith)

/--
Set-theoretic limsup containment for closed-ball global contact sets under
uniform convergence on the closed ball.

In quantified mathematical form, assume that, for every `ε > 0`, there
exists `N` such that, for every `m ≥ N` and every `y ∈ closedBall x0 r`,
`|f_m(y) - f(y)| ≤ ε`. If `δ > 0`, then every point which belongs to

`⋂ k, ⋃ m, ⋃ (_ : k ≤ m), JensenGlobalContactSet f_m x0 r (δ / 2)`

belongs to `JensenContactSet f x0 r δ`.
-/
theorem JensenGlobalContactSet.limsup_subset_jensenContactSet_of_uniformOn_closedBall
    {fseq : Nat -> Point n -> Real} {f : Point n -> Real}
    {x0 : Point n} {r delta : Real}
    (hdelta : 0 < delta)
    (hunif :
      ∀ eps : Real, 0 < eps ->
        ∃ N : Nat, ∀ m : Nat, N <= m ->
          ∀ z : Point n, z ∈ Metric.closedBall x0 r ->
            |fseq m z - f z| <= eps) :
    (⋂ k : Nat, ⋃ m : Nat, ⋃ (_hm : k <= m),
        JensenGlobalContactSet (fseq m) x0 r (delta / 2)) ⊆
      JensenContactSet f x0 r delta := by
  classical
  intro x hx
  simp only [Set.mem_iInter, Set.mem_iUnion] at hx
  let mseq : Nat -> Nat := fun k => Classical.choose (hx k)
  have hmseq : ∀ k : Nat, k <= mseq k := by
    intro k
    exact Classical.choose (Classical.choose_spec (hx k))
  have hxmem :
      ∀ k : Nat, x ∈ JensenGlobalContactSet (fseq (mseq k)) x0 r (delta / 2) := by
    intro k
    exact Classical.choose_spec (Classical.choose_spec (hx k))
  have hxBall : x ∈ Metric.ball x0 r := (hxmem 0).1
  have hxClosed : x ∈ Metric.closedBall x0 r := Metric.ball_subset_closedBall hxBall
  let pseq : Nat -> Point n := fun k => Classical.choose (hxmem k).2
  have hpseq_ball :
      ∀ k : Nat, pseq k ∈ Metric.ball (0 : Point n) (delta / 2) := by
    intro k
    exact (Classical.choose_spec (hxmem k).2).1
  have hmaxseq :
      ∀ k : Nat,
        IsMaxOn (linearPerturbation (fseq (mseq k)) (pseq k))
          (Metric.closedBall x0 r) x := by
    intro k
    exact (Classical.choose_spec (hxmem k).2).2
  have hpseq_closed :
      ∀ k : Nat, pseq k ∈ Metric.closedBall (0 : Point n) (delta / 2) := by
    intro k
    exact Metric.ball_subset_closedBall (hpseq_ball k)
  rcases (isCompact_closedBall (0 : Point n) (delta / 2)).tendsto_subseq hpseq_closed with
    ⟨p, hp_closed, φ, hφ, hp_tendsto⟩
  have hidx : Filter.Tendsto (fun j : Nat => mseq (φ j)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun j : Nat => hmseq (φ j)) hφ.tendsto_atTop
  have hp_delta : p ∈ Metric.ball (0 : Point n) delta := by
    have hhalf_lt : delta / 2 < delta := by linarith
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt hp_closed hhalf_lt
  have hmax : IsMaxOn (linearPerturbation f p) (Metric.closedBall x0 r) x := by
    intro y hy
    have hy_tendsto_f :
        Filter.Tendsto (fun j : Nat => fseq (mseq (φ j)) y)
          Filter.atTop (𝓝 (f y)) :=
      tendsto_eval_of_uniformOn_closedBall_comp
        (n := n) (fseq := fseq) (f := f) (x0 := x0) (r := r)
        (idx := fun j : Nat => mseq (φ j)) hunif hidx hy
    have hx_tendsto_f :
        Filter.Tendsto (fun j : Nat => fseq (mseq (φ j)) x)
          Filter.atTop (𝓝 (f x)) :=
      tendsto_eval_of_uniformOn_closedBall_comp
        (n := n) (fseq := fseq) (f := f) (x0 := x0) (r := r)
        (idx := fun j : Nat => mseq (φ j)) hunif hidx hxClosed
    have hy_tendsto_dot :
        Filter.Tendsto (fun j : Nat => dotProduct (pseq (φ j)) y)
          Filter.atTop (𝓝 (dotProduct p y)) := by
      exact ((continuous_id.dotProduct continuous_const).tendsto p).comp hp_tendsto
    have hx_tendsto_dot :
        Filter.Tendsto (fun j : Nat => dotProduct (pseq (φ j)) x)
          Filter.atTop (𝓝 (dotProduct p x)) := by
      exact ((continuous_id.dotProduct continuous_const).tendsto p).comp hp_tendsto
    have hleft :
        Filter.Tendsto
          (fun j : Nat => linearPerturbation (fseq (mseq (φ j))) (pseq (φ j)) y)
          Filter.atTop (𝓝 (linearPerturbation f p y)) := by
      simpa [linearPerturbation] using hy_tendsto_f.add hy_tendsto_dot
    have hright :
        Filter.Tendsto
          (fun j : Nat => linearPerturbation (fseq (mseq (φ j))) (pseq (φ j)) x)
          Filter.atTop (𝓝 (linearPerturbation f p x)) := by
      simpa [linearPerturbation] using hx_tendsto_f.add hx_tendsto_dot
    exact le_of_tendsto_of_tendsto hleft hright
      (Filter.Eventually.of_forall fun j : Nat => hmaxseq (φ j) hy)
  exact mem_jensenContactSet_of_isMaxOn_closedBall_of_mem_ball
    (n := n) (f := f) (z := x) (x0 := x0) (p := p)
    hxClosed hxBall hp_delta hmax

/--
Under a positive boundary gap, every sufficiently small perturbing vector
produces a point of Jensen's contact set.

In quantified mathematical form, assume `0 ≤ r`, `f` is continuous on
`closedBall x0 r`, every boundary point satisfies
`f x ≤ f x0 - gamma`, `p ∈ ball 0 δ`, and `n ‖p‖ r < gamma`. Then there
exists `z ∈ JensenContactSet f x0 r δ` such that `z` maximizes
`y ↦ f y + p · y` on `closedBall x0 r`, and `z ∈ ball x0 r`.
-/
theorem exists_mem_jensenContactSet_of_boundary_gap
    {f : Point n -> Real} {x0 p : Point n} {r gamma delta : Real}
    (hr : 0 <= r)
    (hf : ContinuousOn f (Metric.closedBall x0 r))
    (hgap :
      ∀ y : Point n, y ∈ Metric.closedBall x0 r -> dist y x0 = r ->
        f y <= f x0 - gamma)
    (hpSmall : (n : Real) * ‖p‖ * r < gamma)
    (hpDelta : p ∈ Metric.ball (0 : Point n) delta) :
    ∃ z : Point n,
      z ∈ JensenContactSet f x0 r delta ∧
        IsMaxOn (linearPerturbation f p) (Metric.closedBall x0 r) z ∧
        z ∈ Metric.ball x0 r := by
  have hne : (Metric.closedBall x0 r).Nonempty := ⟨x0, Metric.mem_closedBall_self hr⟩
  have hlin_cont : ContinuousOn (fun x : Point n => dotProduct p x) (Metric.closedBall x0 r) :=
    (continuous_const.dotProduct continuous_id).continuousOn
  have hpert_cont :
      ContinuousOn (linearPerturbation f p) (Metric.closedBall x0 r) := by
    exact hf.add hlin_cont
  rcases (isCompact_closedBall x0 r).exists_isMaxOn hne hpert_cont with
    ⟨z, hzClosed, hmax⟩
  have hzBall :
      z ∈ Metric.ball x0 r :=
    isMaxOn_linearPerturbation_closedBall_mem_ball_of_boundary_gap
      (n := n) (f := f) (z := z) (x0 := x0) (p := p)
      hr hgap hpSmall hzClosed hmax
  exact ⟨z,
    mem_jensenContactSet_of_isMaxOn_closedBall_of_mem_ball
      (n := n) hzClosed hzBall hpDelta hmax,
    hmax, hzBall⟩

/--
The preceding contact-point existence theorem with the positive boundary gap
supplied by compactness.

In quantified mathematical form, assume `f` is continuous on `closedBall x0 r`
and on `sphere x0 r`, and assume `f x < f x0` for every boundary point. Then
there exists `gamma > 0` such that every `p ∈ ball 0 δ` satisfying
`n ‖p‖ r < gamma` produces a point of `JensenContactSet f x0 r δ` which
maximizes the corresponding linear perturbation on `closedBall x0 r` and
lies in `ball x0 r`.
-/
theorem exists_pos_boundary_gap_forall_small_perturbation_exists_contact
    {f : Point n -> Real} {x0 : Point n} {r : Real}
    (hr : 0 <= r)
    (hfClosed : ContinuousOn f (Metric.closedBall x0 r))
    (hfSphere : ContinuousOn f (Metric.sphere x0 r))
    (hstrict :
      ∀ x : Point n, x ∈ Metric.closedBall x0 r -> dist x x0 = r -> f x < f x0) :
    ∃ gamma : Real, 0 < gamma ∧
      ∀ {delta : Real}, ∀ p : Point n,
        p ∈ Metric.ball (0 : Point n) delta ->
          (n : Real) * ‖p‖ * r < gamma ->
            ∃ z : Point n,
              z ∈ JensenContactSet f x0 r delta ∧
                IsMaxOn (linearPerturbation f p) (Metric.closedBall x0 r) z ∧
                z ∈ Metric.ball x0 r := by
  rcases exists_pos_boundary_gap_of_continuousOn_sphere
      (n := n) (f := f) (x0 := x0) (r := r) hfSphere hstrict with
    ⟨gamma, hgamma_pos, hgap⟩
  refine ⟨gamma, hgamma_pos, ?_⟩
  intro delta p hpDelta hpSmall
  exact exists_mem_jensenContactSet_of_boundary_gap
    (n := n) (f := f) (x0 := x0) (p := p)
    hr hfClosed hgap hpSmall hpDelta

/--
The compact contact-point selection theorem together with first-order
calculus.

In quantified mathematical form, assume `f` is continuous on `closedBall x0 r`
and on `sphere x0 r`, and assume `f x < f x0` for every boundary point. Let
`G : R^n -> R^n` be a function such that, for every `z ∈ ball x0 r`, `f` is
differentiable at `z` with gradient `G z`. Then there exists `gamma > 0` such
that, for every `delta` and every vector `q`, if `q ∈ ball 0 delta` and
`n ‖q‖ r < gamma`, then there exists `z` such that

* `z ∈ JensenContactSet f x0 r delta`;
* `z` maximizes `y ↦ f y + q · y` on `closedBall x0 r`;
* `z ∈ ball x0 r`;
* `G z + q = 0`.
-/
theorem exists_pos_boundary_gap_forall_small_perturbation_exists_contact_gradient
    {f : Point n -> Real} {x0 : Point n} {r : Real} {G : Point n -> Point n}
    (hr : 0 <= r)
    (hfClosed : ContinuousOn f (Metric.closedBall x0 r))
    (hfSphere : ContinuousOn f (Metric.sphere x0 r))
    (hstrict :
      ∀ x : Point n, x ∈ Metric.closedBall x0 r -> dist x x0 = r -> f x < f x0)
    (hderiv :
      ∀ z : Point n, z ∈ Metric.ball x0 r ->
        HasFDerivAt f (gradientLinearMap (G z)) z) :
    ∃ gamma : Real, 0 < gamma ∧
      ∀ {delta : Real}, ∀ q : Point n,
        q ∈ Metric.ball (0 : Point n) delta ->
          (n : Real) * ‖q‖ * r < gamma ->
            ∃ z : Point n,
              z ∈ JensenContactSet f x0 r delta ∧
                IsMaxOn (linearPerturbation f q) (Metric.closedBall x0 r) z ∧
                z ∈ Metric.ball x0 r ∧
                G z + q = 0 := by
  rcases exists_pos_boundary_gap_forall_small_perturbation_exists_contact
      (n := n) (f := f) (x0 := x0) (r := r)
      hr hfClosed hfSphere hstrict with
    ⟨gamma, hgamma_pos, hcontact⟩
  refine ⟨gamma, hgamma_pos, ?_⟩
  intro delta q hqDelta hqSmall
  rcases hcontact q hqDelta hqSmall with ⟨z, hzContact, hmax, hzBall⟩
  have hlocal : IsLocalMax (linearPerturbation f q) z :=
    hmax.isLocalMax (Metric.closedBall_mem_nhds_of_mem hzBall)
  have hgrad :
      G z + q = 0 :=
    gradient_add_eq_zero_of_isLocalMax_linearPerturbation_hasFDerivAt
      (n := n) hlocal (hderiv z hzBall)
  exact ⟨z, hzContact, hmax, hzBall, hgrad⟩

end ViscositySolns
