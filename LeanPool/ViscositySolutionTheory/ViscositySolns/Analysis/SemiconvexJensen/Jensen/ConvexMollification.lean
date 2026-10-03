/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Analysis.SemiconvexJensen.Jensen.ContDiffHessian

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Jensen Contact-Set Theorem (ConvexMollification)

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
Localized Jensen contact-set theorem on a closed ball.

In quantified mathematical form, this says: if `f : R^n -> R` is coordinate
semiconvex on `closedBall x0 r`, `0 < r`, and `f` has a strict local maximum
at `x0`, then for every `delta > 0`, the set of points
`x ∈ closedBall x0 r` for which there exists `p ∈ ball 0 delta` such that
`y ↦ f y + p · y` has a local maximum at `x` has positive Lebesgue measure.
-/
def JensenContactSetPositiveMeasureOnClosedBallTheorem (n : Nat) : Prop :=
  ∀ f : Point n -> Real,
    ∀ x0 : Point n,
    ∀ r : Real, 0 < r ->
      (∃ lambda : Real, CoordinateSemiconvexOn lambda (Metric.closedBall x0 r) f) ->
        StrictLocalMax f x0 ->
          ∀ delta : Real, 0 < delta ->
            0 < volume (JensenContactSet f x0 r delta)

/--
The approximation principle needed to pass from the smooth Jensen theorem to
the localized Jensen contact-set theorem.

In quantified mathematical form, suppose `f : R^n -> R` is coordinate
semiconvex on `closedBall x0 r`, `0 < r`, and `f x < f x0` for every
`x ∈ closedBall x0 r` with `x ≠ x0`. For every `delta > 0`, there exists a
sequence of functions `f_m : R^n -> R` and a number `c > 0` such that:

* every set `JensenContactSet f_m x0 r (delta / 2)` is measurable;
* the set-theoretic limsup
  `⋂ k, ⋃ m, ⋃ (_ : k ≤ m), JensenContactSet f_m x0 r (delta / 2)`
  is contained in `JensenContactSet f x0 r delta`;
* for every `m`, the measure of `JensenContactSet f_m x0 r (delta / 2)` is
  at least `c`.

This is the exact nonsmooth approximation statement needed by the
measure-theoretic limsup lemma below. The smaller perturbation radius
`delta / 2` leaves room to pass perturbing vectors to a limit while remaining
inside `Metric.ball 0 delta`.
-/
def JensenContactSetLimsupApproximationPrincipleOnClosedBall (n : Nat) : Prop :=
  ∀ f : Point n -> Real,
    ∀ x0 : Point n,
    ∀ r : Real, 0 < r ->
      (∃ lambda : Real, CoordinateSemiconvexOn lambda (Metric.closedBall x0 r) f) ->
        (∀ x : Point n, x ∈ Metric.closedBall x0 r -> x ≠ x0 -> f x < f x0) ->
          ∀ delta : Real, 0 < delta ->
            ∃ fseq : Nat -> Point n -> Real,
            ∃ c : ℝ≥0∞,
              0 < c ∧
                (∀ m : Nat,
                  MeasurableSet (JensenContactSet (fseq m) x0 r (delta / 2))) ∧
                ((⋂ k : Nat, ⋃ m : Nat, ⋃ (_hm : k <= m),
                    JensenContactSet (fseq m) x0 r (delta / 2)) ⊆
                    JensenContactSet f x0 r delta) ∧
                (∀ m : Nat,
                  c <= volume (JensenContactSet (fseq m) x0 r (delta / 2)))

/--
The approximation principle in the form closest to the proof in the paper.

In quantified mathematical form, suppose `f : R^n -> R` is coordinate
semiconvex on `closedBall x0 r`, `0 < r`, and `f x < f x0` for every
`x ∈ closedBall x0 r` with `x ≠ x0`. For every `delta > 0`, there exists a
sequence of functions `f_m : R^n -> R` and a number `c > 0` such that:

* every set `JensenGlobalContactSet f_m x0 r (delta / 2)` is measurable;
* the set-theoretic limsup
  `⋂ k, ⋃ m, ⋃ (_ : k ≤ m),
    JensenGlobalContactSet f_m x0 r (delta / 2)`
  is contained in `JensenContactSet f x0 r delta`;
* for every `m`, the measure of
  `JensenGlobalContactSet f_m x0 r (delta / 2)` is at least `c`.

Here `JensenGlobalContactSet f_m x0 r (delta / 2)` consists of the points in
`ball x0 r` which maximize `y ↦ f_m y + p · y` on `closedBall x0 r` for some
`p ∈ ball 0 (delta / 2)`. The use of `delta / 2` leaves a positive margin
when passing perturbing vectors to a limit.
-/
def JensenGlobalContactSetLimsupApproximationPrincipleOnClosedBall (n : Nat) : Prop :=
  ∀ f : Point n -> Real,
    ∀ x0 : Point n,
    ∀ r : Real, 0 < r ->
      (∃ lambda : Real, CoordinateSemiconvexOn lambda (Metric.closedBall x0 r) f) ->
        (∀ x : Point n, x ∈ Metric.closedBall x0 r -> x ≠ x0 -> f x < f x0) ->
          ∀ delta : Real, 0 < delta ->
            ∃ fseq : Nat -> Point n -> Real,
            ∃ c : ℝ≥0∞,
              0 < c ∧
                (∀ m : Nat,
                  MeasurableSet (JensenGlobalContactSet (fseq m) x0 r (delta / 2))) ∧
                ((⋂ k : Nat, ⋃ m : Nat, ⋃ (_hm : k <= m),
                    JensenGlobalContactSet (fseq m) x0 r (delta / 2)) ⊆
                    JensenContactSet f x0 r delta) ∧
                (∀ m : Nat,
                  c <= volume (JensenGlobalContactSet (fseq m) x0 r (delta / 2)))

/--
The source-aligned global-contact approximation principle with semiconvexity
available on a larger closed ball.

In quantified mathematical form, suppose `0 < r`, `r < R`, `f : R^n -> R`
is coordinate semiconvex on `closedBall x0 R`, and
`f x < f x0` for every `x ∈ closedBall x0 r` with `x ≠ x0`. For every
`delta > 0`, there exists a sequence of functions `f_m : R^n -> R` and a
number `c > 0` such that:

* every set `JensenGlobalContactSet f_m x0 r (delta / 2)` is measurable;
* the set-theoretic limsup
  `⋂ k, ⋃ m, ⋃ (_ : k ≤ m),
    JensenGlobalContactSet f_m x0 r (delta / 2)`
  is contained in `JensenContactSet f x0 r delta`;
* for every `m`, the measure of
  `JensenGlobalContactSet f_m x0 r (delta / 2)` is at least `c`.

The strict inequality `r < R` is the formal version of the source proof's
choice of a smaller closed ball inside a region where the semiconvex function
is defined. It gives continuity on the boundary sphere of radius `r`.
-/
def JensenGlobalContactSetInteriorLimsupApproximationPrincipleOnClosedBall
    (n : Nat) : Prop :=
  ∀ f : Point n -> Real,
    ∀ x0 : Point n,
    ∀ R r : Real, 0 < r -> r < R ->
      (∃ lambda : Real, CoordinateSemiconvexOn lambda (Metric.closedBall x0 R) f) ->
        (∀ x : Point n, x ∈ Metric.closedBall x0 r -> x ≠ x0 -> f x < f x0) ->
          ∀ delta : Real, 0 < delta ->
            ∃ fseq : Nat -> Point n -> Real,
            ∃ c : ℝ≥0∞,
              0 < c ∧
                (∀ m : Nat,
                  MeasurableSet (JensenGlobalContactSet (fseq m) x0 r (delta / 2))) ∧
                ((⋂ k : Nat, ⋃ m : Nat, ⋃ (_hm : k <= m),
                    JensenGlobalContactSet (fseq m) x0 r (delta / 2)) ⊆
                    JensenContactSet f x0 r delta) ∧
                (∀ m : Nat,
                  c <= volume (JensenGlobalContactSet (fseq m) x0 r (delta / 2)))

/--
The remaining smooth convex approximation theorem needed for the
mollification step.

In quantified mathematical form, suppose `0 < r`, `r < R`, and
`g : R^n -> R` is convex on `closedBall x0 R`. Then there should be smooth
functions `g_m : R^n -> R` such that:

* for every `ε > 0`, there is a natural number `N` such that for every
  `m ≥ N` and every `z ∈ closedBall x0 r`,
  `|g_m z - g z| ≤ ε`;
* every `g_m` is twice continuously differentiable;
* every `g_m` is convex on `closedBall x0 r`.

This is the analytic mollification theorem for convex functions, stated
separately from the viscosity-solution notation. It is stronger than ordinary
smooth approximation because convexity must be preserved on the closed ball
where the Jensen contact-set estimate is applied.
-/
def SmoothConvexApproximationOnInteriorClosedBallTheorem (n : Nat) : Prop :=
  ∀ g : Point n -> Real,
    ∀ x0 : Point n,
    ∀ R r : Real, 0 < r -> r < R ->
      ConvexOn Real (Metric.closedBall x0 R) g ->
        ∃ gseq : Nat -> Point n -> Real,
          (∀ eps : Real, 0 < eps ->
            ∃ N : Nat, ∀ m : Nat, N <= m ->
              ∀ z : Point n, z ∈ Metric.closedBall x0 r ->
              |gseq m z - g z| <= eps) ∧
          (∀ m : Nat, ContDiff Real (2 : ℕ∞ω) (gseq m)) ∧
          (∀ m : Nat, ConvexOn Real (Metric.closedBall x0 r) (gseq m))

/--
Convexity on a closed ball supplies a continuous extension from an
intermediate closed ball to the whole ambient coordinate space.

In quantified mathematical form, suppose `0 < r`, `r < R`, and
`g : R^n -> R` is convex on `closedBall x0 R`. Then there exists a radius
`Rmid` satisfying `r < Rmid < R` and a continuous function
`G : R^n -> R` such that `G x = g x` for every
`x ∈ closedBall x0 Rmid`.

This is the extension step used before mollification. The intermediate
radius ensures that convolution kernels with sufficiently small support do
not sample outside the region on which the original convex function is known.
-/
theorem exists_continuous_extension_eqOn_intermediate_closedBall_of_convexOn_closedBall
    {g : Point n -> Real} {x0 : Point n} {R r : Real}
    (_hr : 0 < r) (hrR : r < R)
    (hconv : ConvexOn Real (Metric.closedBall x0 R) g) :
    ∃ Rmid : Real,
      r < Rmid ∧ Rmid < R ∧
        ∃ G : Point n -> Real,
          Continuous G ∧
            ∀ x : Point n, x ∈ Metric.closedBall x0 Rmid -> G x = g x := by
  let Rmid : Real := (r + R) / 2
  have hrRmid : r < Rmid := by
    dsimp [Rmid]
    linarith
  have hRmidR : Rmid < R := by
    dsimp [Rmid]
    linarith
  let s : Set (Point n) := Metric.closedBall x0 Rmid
  have hcont_ball : ContinuousOn g (Metric.ball x0 R) :=
    (ConvexOn.coordinateSemiconvexOn_zero (n := n) hconv).continuousOn_ball_of_closedBall
  have hsub : s ⊆ Metric.ball x0 R := by
    intro x hx
    exact Metric.closedBall_subset_ball hRmidR hx
  have hcont_s : ContinuousOn g s :=
    hcont_ball.mono hsub
  let grestrict : C(s, Real) :=
    ⟨fun x : s => g x, continuousOn_iff_continuous_domRestrict.mp hcont_s⟩
  rcases ContinuousMap.exists_restrict_eq (Y := Real) Metric.isClosed_closedBall grestrict with
    ⟨G, hG⟩
  refine ⟨Rmid, hrRmid, hRmidR, G, G.continuous, ?_⟩
  intro x hx
  have hfun :
      (G.restrict s : s -> Real) = (grestrict : s -> Real) := by
    exact congrArg (fun F : C(s, Real) => (F : s -> Real)) hG
  have hx_eq := congrFun hfun ⟨x, hx⟩
  exact hx_eq

/--
The remaining convolution-only smooth approximation theorem after extending
the convex function to a continuous function on the whole space.

In quantified mathematical form, suppose `0 < r`, `r < R`,
`g : R^n -> R` is convex on `closedBall x0 R`, and `G : R^n -> R` is
continuous on all of `R^n` and agrees with `g` on `closedBall x0 R`. Then
there are functions `g_m : R^n -> R` such that:

* for every `ε > 0`, there exists `N` such that for every `m ≥ N` and every
  `z ∈ closedBall x0 r`, `|g_m z - g z| ≤ ε`;
* every `g_m` is twice continuously differentiable;
* every `g_m` is convex on `closedBall x0 r`.

The intended proof is by convolution of `G` with nonnegative smooth kernels
whose supports are eventually contained in a ball of radius smaller than
`R - r`. The equality `G = g` on `closedBall x0 R` then ensures that, on
`closedBall x0 r`, the convolution only uses values where the original
function is convex.
-/
def ContinuousExtensionConvexMollificationOnInteriorClosedBallTheorem
    (n : Nat) : Prop :=
  ∀ g G : Point n -> Real,
    ∀ x0 : Point n,
    ∀ R r : Real, 0 < r -> r < R ->
      ConvexOn Real (Metric.closedBall x0 R) g ->
        Continuous G ->
          (∀ x : Point n, x ∈ Metric.closedBall x0 R -> G x = g x) ->
            ∃ gseq : Nat -> Point n -> Real,
              (∀ eps : Real, 0 < eps ->
                ∃ N : Nat, ∀ m : Nat, N <= m ->
                  ∀ z : Point n, z ∈ Metric.closedBall x0 r ->
                    |gseq m z - g z| <= eps) ∧
              (∀ m : Nat, ContDiff Real (2 : ℕ∞ω) (gseq m)) ∧
              (∀ m : Nat, ConvexOn Real (Metric.closedBall x0 r) (gseq m))

/--
The continuous-extension convolution theorem implies smooth convex
approximation on interior closed balls.

In quantified mathematical form, start with a convex function on
`closedBall x0 R` and choose an intermediate radius `Rmid` with
`r < Rmid < R`. The extension theorem gives a continuous function on the
ambient space agreeing with the original convex function on
`closedBall x0 Rmid`; the convolution theorem applied on the pair of radii
`r < Rmid` gives the desired smooth convex approximants on
`closedBall x0 r`.
-/
theorem SmoothConvexApproximationOnInteriorClosedBallTheorem.of_extensionMollification
    (hmoll : ContinuousExtensionConvexMollificationOnInteriorClosedBallTheorem n) :
    SmoothConvexApproximationOnInteriorClosedBallTheorem n := by
  intro g x0 R r hr hrR hconv
  rcases exists_continuous_extension_eqOn_intermediate_closedBall_of_convexOn_closedBall
      (n := n) (g := g) (x0 := x0) (R := R) (r := r) hr hrR hconv with
    ⟨Rmid, hrRmid, hRmidR, G, hGcont, hGeq⟩
  have hconv_mid : ConvexOn Real (Metric.closedBall x0 Rmid) g :=
    hconv.subset
      (Metric.closedBall_subset_closedBall (le_of_lt hRmidR))
      (convex_closedBall x0 Rmid)
  exact hmoll g G x0 Rmid r hr hrRmid hconv_mid hGcont hGeq

/--
Convolution with a normalized smooth bump is twice continuously
differentiable in the spatial variable.

In quantified mathematical form, if `G : R^n -> R` is continuous and
`φ` is a compactly supported smooth bump function centered at the origin,
then
`x ↦ ∫ φ(z) G(x - z) dz`, normalized by the Haar measure integral of `φ`,
is `C^2`.
-/
theorem contDiff_two_normedBumpConvolution_left
    (φ : ContDiffBump (0 : Point n)) {G : Point n -> Real}
    (hG : Continuous G) :
    ContDiff Real (2 : ℕ∞ω)
      (φ.normed volume ⋆[lsmul Real Real, volume] G : Point n -> Real) := by
  have hloc : LocallyIntegrable G volume :=
    hG.locallyIntegrable
  exact φ.hasCompactSupport_normed.contDiff_convolution_left
    (L := lsmul Real Real) φ.contDiff_normed hloc

/--
A ball centered at a point of a smaller closed ball is contained in a larger
closed ball if the two radii satisfy the corresponding triangle inequality.

In quantified mathematical form, if `z ∈ closedBall x0 r` and `r + ρ ≤ R`,
then every point in `ball z ρ` belongs to `closedBall x0 R`.
-/
theorem ball_subset_closedBall_of_mem_closedBall_add_le
    {x0 z : Point n} {r R ρ : Real}
    (hz : z ∈ Metric.closedBall x0 r) (hρR : r + ρ <= R) :
    Metric.ball z ρ ⊆ Metric.closedBall x0 R := by
  intro y hy
  have hyz : dist y z < ρ := by
    simpa [Metric.mem_ball] using hy
  have hzx : dist z x0 <= r := by
    simpa [Metric.mem_closedBall] using hz
  have hyx : dist y x0 <= dist y z + dist z x0 :=
    dist_triangle y z x0
  have hsum : dist y z + dist z x0 <= ρ + r := by
    exact add_le_add hyz.le hzx
  have htarget : dist y x0 <= R := by
    linarith
  simpa [Metric.mem_closedBall] using htarget

/--
Subtracting a vector in a small ball from a point of the smaller closed ball
keeps the result in the larger closed ball.

In quantified mathematical form, if `x ∈ closedBall x0 r`, `z ∈ ball 0 ρ`,
and `r + ρ ≤ R`, then `x - z ∈ closedBall x0 R`.
-/
theorem sub_mem_closedBall_of_mem_closedBall_mem_ball_add_le
    {x0 x z : Point n} {r R ρ : Real}
    (hx : x ∈ Metric.closedBall x0 r) (hz : z ∈ Metric.ball (0 : Point n) ρ)
    (hρR : r + ρ <= R) :
    x - z ∈ Metric.closedBall x0 R := by
  have hdist_z : dist z (0 : Point n) < ρ := by
    simpa [Metric.mem_ball] using hz
  have hdist_x : dist x x0 <= r := by
    simpa [Metric.mem_closedBall] using hx
  have hdist :
      dist (x - z) x0 <= dist (x - z) x + dist x x0 :=
    dist_triangle (x - z) x x0
  have hsub : dist (x - z) x = dist z (0 : Point n) := by
    rw [dist_eq_norm, dist_eq_norm]
    simp [sub_eq_add_neg, add_comm, add_left_comm]
  have htarget : dist (x - z) x0 <= R := by
    rw [hsub] at hdist
    linarith
  simpa [Metric.mem_closedBall] using htarget

/--
The convolution sample points used in the convexity argument lie in the
larger closed ball.

In quantified mathematical form, assume `x,y ∈ closedBall x0 r`,
`a,b ≥ 0`, `a+b=1`, `z ∈ ball 0 ρ`, and `r + ρ ≤ R`. Then
`x - z`, `y - z`, and `a • x + b • y - z` all belong to
`closedBall x0 R`.
-/
theorem convexCombination_sub_mem_closedBall_of_mem_closedBall_mem_ball_add_le
    {x0 x y z : Point n} {r R ρ a b : Real}
    (hx : x ∈ Metric.closedBall x0 r) (hy : y ∈ Metric.closedBall x0 r)
    (ha : 0 <= a) (hb : 0 <= b) (hab : a + b = 1)
    (hz : z ∈ Metric.ball (0 : Point n) ρ) (hρR : r + ρ <= R) :
    (x - z ∈ Metric.closedBall x0 R) ∧
      (y - z ∈ Metric.closedBall x0 R) ∧
        (a • x + b • y - z ∈ Metric.closedBall x0 R) := by
  have hxy : a • x + b • y ∈ Metric.closedBall x0 r := by
    exact (convex_closedBall x0 r) hx hy ha hb hab
  exact
    ⟨sub_mem_closedBall_of_mem_closedBall_mem_ball_add_le
        (x0 := x0) (x := x) (z := z) (r := r) (R := R) (ρ := ρ)
        hx hz hρR,
      sub_mem_closedBall_of_mem_closedBall_mem_ball_add_le
        (x0 := x0) (x := y) (z := z) (r := r) (R := R) (ρ := ρ)
        hy hz hρR,
      sub_mem_closedBall_of_mem_closedBall_mem_ball_add_le
        (x0 := x0) (x := a • x + b • y) (z := z) (r := r) (R := R) (ρ := ρ)
        hxy hz hρR⟩

/--
The pointwise convexity inequality for the convolution integrand.

In quantified mathematical form, suppose `G = g` on `closedBall x0 R`,
`g` is convex on `closedBall x0 R`, and the translated sample points
`x - z`, `y - z`, and `a x + b y - z` lie in this closed ball. Then the
corresponding values of `G` satisfy the convexity inequality.
-/
theorem convolution_sample_convexity_inequality
    {g G : Point n -> Real} {x0 x y z : Point n} {R a b : Real}
    (hconv : ConvexOn Real (Metric.closedBall x0 R) g)
    (hGeq : ∀ w : Point n, w ∈ Metric.closedBall x0 R -> G w = g w)
    (hxz : x - z ∈ Metric.closedBall x0 R)
    (hyz : y - z ∈ Metric.closedBall x0 R)
    (hxyz : a • x + b • y - z ∈ Metric.closedBall x0 R)
    (ha : 0 <= a) (hb : 0 <= b) (hab : a + b = 1) :
    G (a • x + b • y - z) <= a * G (x - z) + b * G (y - z) := by
  have hlin :
      a • (x - z) + b • (y - z) = a • x + b • y - z := by
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    ring_nf
    have hzab : z i * a + z i * b = z i := by
      rw [← mul_add, hab, mul_one]
    linarith
  have hconv_le :
      g (a • (x - z) + b • (y - z)) <=
        a • g (x - z) + b • g (y - z) :=
    hconv.2 hxz hyz ha hb hab
  rw [hlin] at hconv_le
  simpa [hGeq (a • x + b • y - z) hxyz, hGeq (x - z) hxz,
    hGeq (y - z) hyz, smul_eq_mul] using hconv_le

/--
Fixed-kernel convexity preservation for normalized bump convolution.

In quantified mathematical form, suppose `g` is convex on `closedBall x0 R`,
`G = g` on this closed ball, and the outer support radius of the bump is at
most `R - r`. Then the normalized convolution of `G` with this bump is
convex on `closedBall x0 r`.
-/
theorem convexOn_normedBumpConvolution_of_convexOn_extension
    (φ : ContDiffBump (0 : Point n)) {g G : Point n -> Real}
    (hG : Continuous G) {x0 : Point n} {R r : Real}
    (hconv : ConvexOn Real (Metric.closedBall x0 R) g)
    (hGeq : ∀ w : Point n, w ∈ Metric.closedBall x0 R -> G w = g w)
    (hcontain : r + φ.rOut <= R) :
    ConvexOn Real (Metric.closedBall x0 r)
      (φ.normed volume ⋆[lsmul Real Real, volume] G : Point n -> Real) := by
  let k : Point n -> Real := φ.normed volume
  let F : Point n -> Real := k ⋆[lsmul Real Real, volume] G
  have hk_nonneg : ∀ z : Point n, 0 <= k z := by
    intro z
    exact φ.nonneg_normed z
  have hk_cont : Continuous k := by
    exact (φ.contDiff_normed (n := (⊤ : ℕ∞))).continuous
  have hG_loc : LocallyIntegrable G volume :=
    hG.locallyIntegrable
  have hconv_exists : ConvolutionExists k G (lsmul Real Real) volume :=
    φ.hasCompactSupport_normed.convolutionExists_left
      (L := lsmul Real Real) hk_cont hG_loc
  refine ⟨convex_closedBall x0 r, ?_⟩
  intro x hx y hy a b ha hb hab
  let p : Point n := a • x + b • y
  have hp : p ∈ Metric.closedBall x0 r :=
    (convex_closedBall x0 r) hx hy ha hb hab
  have hIp : Integrable (fun z : Point n => k z * G (p - z)) volume := by
    exact hconv_exists p
  have hIx : Integrable (fun z : Point n => k z * G (x - z)) volume := by
    exact hconv_exists x
  have hIy : Integrable (fun z : Point n => k z * G (y - z)) volume := by
    exact hconv_exists y
  have hRight :
      Integrable
        (fun z : Point n => k z * (a * G (x - z) + b * G (y - z))) volume := by
    have hxint : Integrable (fun z : Point n => a * (k z * G (x - z))) volume :=
      hIx.const_mul a
    have hyint : Integrable (fun z : Point n => b * (k z * G (y - z))) volume :=
      hIy.const_mul b
    refine (hxint.add hyint).congr ?_
    filter_upwards with z
    simp only [Pi.add_apply]
    ring_nf
  have hpoint :
      ∀ z : Point n,
        k z * G (p - z) <= k z * (a * G (x - z) + b * G (y - z)) := by
    intro z
    by_cases hz : z ∈ Function.support k
    · have hz_ball : z ∈ Metric.ball (0 : Point n) φ.rOut := by
        simpa [k, φ.support_normed_eq] using hz
      rcases convexCombination_sub_mem_closedBall_of_mem_closedBall_mem_ball_add_le
          (x0 := x0) (x := x) (y := y) (z := z) (r := r) (R := R)
          (ρ := φ.rOut) (a := a) (b := b)
          hx hy ha hb hab hz_ball hcontain with
        ⟨hxz, hyz, hpz⟩
      have hle :
          G (p - z) <= a * G (x - z) + b * G (y - z) := by
        simpa [p] using
          convolution_sample_convexity_inequality
            (n := n) (g := g) (G := G) (x0 := x0) (x := x) (y := y)
            (z := z) (R := R) (a := a) (b := b)
            hconv hGeq hxz hyz hpz ha hb hab
      exact mul_le_mul_of_nonneg_left hle (hk_nonneg z)
    · have hkz : k z = 0 := by
        simpa [Function.mem_support] using hz
      simp [hkz]
  have hint_le :
      (∫ z : Point n, k z * G (p - z) ∂volume) <=
        ∫ z : Point n, k z * (a * G (x - z) + b * G (y - z)) ∂volume :=
    integral_mono hIp hRight hpoint
  have hright_eval :
      (∫ z : Point n, k z * (a * G (x - z) + b * G (y - z)) ∂volume) =
        a * (∫ z : Point n, k z * G (x - z) ∂volume) +
          b * (∫ z : Point n, k z * G (y - z) ∂volume) := by
    calc
      (∫ z : Point n, k z * (a * G (x - z) + b * G (y - z)) ∂volume)
          = ∫ z : Point n, (a * (k z * G (x - z)) +
              b * (k z * G (y - z))) ∂volume := by
            congr
            ext z
            ring
      _ = (∫ z : Point n, a * (k z * G (x - z)) ∂volume) +
            ∫ z : Point n, b * (k z * G (y - z)) ∂volume := by
            rw [integral_add (hIx.const_mul a) (hIy.const_mul b)]
      _ = a * (∫ z : Point n, k z * G (x - z) ∂volume) +
            b * (∫ z : Point n, k z * G (y - z) ∂volume) := by
            rw [integral_const_mul, integral_const_mul]
  have hFx :
      F x = ∫ z : Point n, k z * G (x - z) ∂volume := by
    rfl
  have hFy :
      F y = ∫ z : Point n, k z * G (y - z) ∂volume := by
    rfl
  have hFp :
      F p = ∫ z : Point n, k z * G (p - z) ∂volume := by
    rfl
  calc
    F (a • x + b • y) = F p := rfl
    _ <= a * F x + b * F y := by
      rw [hFp, hFx, hFy]
      exact hint_le.trans_eq hright_eval

/--
The fixed-kernel uniform approximation estimate for normalized bump
convolution.

In quantified mathematical form, let `G : R^n -> R` be continuous and let
`φ` be a normalized smooth bump. If, for every `z ∈ closedBall x0 r`, the
oscillation of `G` on `ball z φ.rOut` is at most `ε`, then the convolution
of `G` with `φ.normed volume` differs from `G` by at most `ε` at every
`z ∈ closedBall x0 r`.
-/
theorem abs_normedBumpConvolution_sub_le_of_local_oscillation
    (φ : ContDiffBump (0 : Point n)) {G : Point n -> Real}
    (hG : Continuous G) {x0 : Point n} {r eps : Real}
    (hosc :
      ∀ z : Point n, z ∈ Metric.closedBall x0 r ->
        ∀ y : Point n, y ∈ Metric.ball z φ.rOut -> dist (G y) (G z) <= eps) :
    ∀ z : Point n, z ∈ Metric.closedBall x0 r ->
      |(φ.normed volume ⋆[lsmul Real Real, volume] G : Point n -> Real) z - G z| <=
        eps := by
  intro z hz
  have hdist :
      dist ((φ.normed volume ⋆[lsmul Real Real, volume] G : Point n -> Real) z) (G z) <=
        eps :=
    φ.dist_normed_convolution_le hG.aestronglyMeasurable (hosc z hz)
  simpa [Real.dist_eq] using hdist

/--
The fixed-kernel approximation estimate, rewritten for a function `g` which
agrees with the continuous extension `G` on a closed ball containing all
points sampled by the kernel.

In quantified mathematical form, suppose `G = g` on `closedBall x0 R`, every
point in `closedBall x0 r` is at distance at least `φ.rOut` from the outside
of `closedBall x0 R`, and `G` varies by at most `ε` on the balls
`ball z φ.rOut` centered at points `z ∈ closedBall x0 r`. Then the normalized
bump convolution of `G` is within `ε` of `g` on `closedBall x0 r`.
-/
theorem abs_normedBumpConvolution_sub_extension_le_of_local_oscillation
    (φ : ContDiffBump (0 : Point n)) {g G : Point n -> Real}
    (hG : Continuous G) {x0 : Point n} {R r eps : Real}
    (hGeq : ∀ x : Point n, x ∈ Metric.closedBall x0 R -> G x = g x)
    (hcontain : r + φ.rOut <= R)
    (hosc :
      ∀ z : Point n, z ∈ Metric.closedBall x0 r ->
        ∀ y : Point n, y ∈ Metric.ball z φ.rOut -> dist (G y) (G z) <= eps) :
    ∀ z : Point n, z ∈ Metric.closedBall x0 r ->
      |(φ.normed volume ⋆[lsmul Real Real, volume] G : Point n -> Real) z - g z| <=
        eps := by
  intro z hz
  have hzR : z ∈ Metric.closedBall x0 R :=
    ball_subset_closedBall_of_mem_closedBall_add_le
      (x0 := x0) (z := z) (r := r) (R := R) (ρ := φ.rOut)
      hz hcontain (Metric.mem_ball_self φ.rOut_pos)
  have hbase :
      |(φ.normed volume ⋆[lsmul Real Real, volume] G : Point n -> Real) z - G z| <=
        eps :=
    abs_normedBumpConvolution_sub_le_of_local_oscillation
      (n := n) φ hG hosc z hz
  simpa [hGeq z hzR] using hbase

/--
Compact uniform continuity supplies a support radius for the local
oscillation estimate used by mollification.

In quantified mathematical form, suppose `G : R^n -> R` is continuous,
`0 < r < R`, and `ε > 0`. Then there exists `η > 0` such that
`η ≤ R - r` and, for every `z ∈ closedBall x0 r`, every point
`y ∈ ball z η` satisfies `dist (G y) (G z) ≤ ε`.
-/
theorem exists_pos_le_sub_forall_dist_le_of_continuous_on_closedBall
    {G : Point n -> Real} (hG : Continuous G)
    {x0 : Point n} {R r eps : Real} (hrR : r < R) (heps : 0 < eps) :
    ∃ η : Real,
      0 < η ∧ η <= R - r ∧
        ∀ z : Point n, z ∈ Metric.closedBall x0 r ->
          ∀ y : Point n, y ∈ Metric.ball z η -> dist (G y) (G z) <= eps := by
  have huc : UniformContinuousOn G (Metric.closedBall x0 R) :=
    (isCompact_closedBall x0 R).uniformContinuousOn_of_continuous hG.continuousOn
  rcases Metric.uniformContinuousOn_iff_le.mp huc eps heps with
    ⟨δ, hδ_pos, hδ⟩
  let η : Real := min δ (R - r) / 2
  have hmargin_pos : 0 < R - r := by
    linarith
  have hmin_pos : 0 < min δ (R - r) :=
    lt_min hδ_pos hmargin_pos
  have hη_pos : 0 < η := by
    dsimp [η]
    linarith
  have hη_le_delta : η <= δ := by
    dsimp [η]
    have hmin_le : min δ (R - r) <= δ := min_le_left _ _
    linarith
  have hη_le_margin : η <= R - r := by
    dsimp [η]
    have hmin_le : min δ (R - r) <= R - r := min_le_right _ _
    linarith
  refine ⟨η, hη_pos, hη_le_margin, ?_⟩
  intro z hz y hy
  have hzR : z ∈ Metric.closedBall x0 R := by
    exact Metric.closedBall_subset_closedBall (by linarith) hz
  have hyR : y ∈ Metric.closedBall x0 R := by
    have hcontain : r + η <= R := by
      linarith
    exact ball_subset_closedBall_of_mem_closedBall_add_le
          (x0 := x0) (z := z) (r := r) (R := R) (ρ := η)
      hz hcontain hy
  have hyz_le : dist y z <= δ := by
    have hyz_lt : dist y z < η := by
      simpa [Metric.mem_ball] using hy
    exact le_trans hyz_lt.le hη_le_delta
  have hzy_le : dist z y <= δ := by
    simpa [dist_comm] using hyz_le
  simpa [dist_comm] using hδ z hzR y hyR hzy_le

/--
Uniform approximation by any sufficiently small normalized bump convolution.

In quantified mathematical form, suppose `G = g` on `closedBall x0 R`,
`G` is continuous, and `0 < r < R`. For every `ε > 0`, there exists
`η > 0` such that, for every smooth bump `φ` centered at the origin with
outer support radius at most `η`, the normalized convolution of `G` with
`φ` is within `ε` of `g` at every point of `closedBall x0 r`.
-/
theorem exists_pos_forall_rOut_le_abs_normedBumpConvolution_sub_extension_le
    {g G : Point n -> Real} (hG : Continuous G)
    {x0 : Point n} {R r eps : Real} (hrR : r < R) (heps : 0 < eps)
    (hGeq : ∀ x : Point n, x ∈ Metric.closedBall x0 R -> G x = g x) :
    ∃ η : Real,
      0 < η ∧
        ∀ φ : ContDiffBump (0 : Point n), φ.rOut <= η ->
          ∀ z : Point n, z ∈ Metric.closedBall x0 r ->
            |(φ.normed volume ⋆[lsmul Real Real, volume] G : Point n -> Real) z - g z| <=
              eps := by
  rcases exists_pos_le_sub_forall_dist_le_of_continuous_on_closedBall
      (n := n) (G := G) hG (x0 := x0) (R := R) (r := r) hrR heps with
    ⟨η, hη_pos, hη_le_margin, hoscη⟩
  refine ⟨η, hη_pos, ?_⟩
  intro φ hφη z hz
  have hcontain : r + φ.rOut <= R := by
    linarith
  have hoscφ :
      ∀ z : Point n, z ∈ Metric.closedBall x0 r ->
        ∀ y : Point n, y ∈ Metric.ball z φ.rOut -> dist (G y) (G z) <= eps := by
    intro w hw y hy
    apply hoscη w hw y
    have hy_dist : dist y w < φ.rOut := by
      simpa [Metric.mem_ball] using hy
    exact Metric.mem_ball.2 (lt_of_lt_of_le hy_dist hφη)
  exact abs_normedBumpConvolution_sub_extension_le_of_local_oscillation
    (n := n) φ hG hGeq hcontain hoscφ z hz

/--
A concrete family of smooth bump functions whose outer support radii are
`rho / (m + 1)`.

In quantified mathematical form, if `rho > 0`, then for each natural number
`m` this is a smooth bump centered at the origin, with inner radius
`rho / (2 * (m + 1))` and outer radius `rho / (m + 1)`.
-/
def jensenMollifierBump (n : Nat) (rho : Real) (hrho : 0 < rho) (m : Nat) :
    ContDiffBump (0 : Point n) :=
  let rOut : Real := rho / ((m : Real) + 1)
  have hrOut_pos : 0 < rOut := by
    dsimp [rOut]
    positivity
  ⟨rOut / 2, rOut, half_pos hrOut_pos, half_lt_self hrOut_pos⟩

@[simp]
theorem jensenMollifierBump_rOut
    (rho : Real) (hrho : 0 < rho) (m : Nat) :
    (jensenMollifierBump n rho hrho m).rOut = rho / ((m : Real) + 1) := by
  rfl

/--
The outer support radii of `jensenMollifierBump n rho hrho m` converge to
zero as `m -> ∞`.
-/
theorem tendsto_jensenMollifierBump_rOut
    (rho : Real) (hrho : 0 < rho) :
    Filter.Tendsto
      (fun m : Nat => (jensenMollifierBump n rho hrho m).rOut)
      Filter.atTop (𝓝 0) := by
  simpa [jensenMollifierBump, div_eq_mul_inv, one_div] using
    (tendsto_const_nhds.mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real) : Filter.Tendsto
        (fun m : Nat => (1 : Real) / ((m : Real) + 1)) Filter.atTop (𝓝 0)))

/--
For fixed positive `rho`, every outer support radius
`rho / (m + 1)` is bounded above by `rho`.
-/
theorem jensenMollifierBump_rOut_le_rho
    (rho : Real) (hrho : 0 < rho) (m : Nat) :
    (jensenMollifierBump n rho hrho m).rOut <= rho := by
  have hden_pos : 0 < (m : Real) + 1 := by positivity
  have hden_ge : 1 <= (m : Real) + 1 := by
    have hm_nonneg : 0 <= (m : Real) := Nat.cast_nonneg m
    linarith
  rw [jensenMollifierBump_rOut]
  rw [div_le_iff₀ hden_pos]
  nlinarith [mul_le_mul_of_nonneg_left hden_ge hrho.le]

end ViscositySolns
