/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Analysis.SemiconvexJensen.Jensen.ConvexMollification

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Jensen Contact-Set Theorem (MainTheorems)

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
The continuous-extension convolution theorem.

In quantified mathematical form, suppose `0 < r < R`, `g` is convex on
`closedBall x0 R`, `G` is continuous on all of `R^n`, and `G = g` on
`closedBall x0 R`. Choose `rho = (R - r) / 2`. The functions

`g_m = (jensenMollifierBump n rho _ m).normed volume ⋆ G`

converge uniformly to `g` on `closedBall x0 r`, are twice continuously
differentiable, and are convex on `closedBall x0 r`.
-/
theorem ContinuousExtensionConvexMollificationOnInteriorClosedBallTheorem.proof :
    ContinuousExtensionConvexMollificationOnInteriorClosedBallTheorem n := by
  intro g G x0 R r hr hrR hconv hG hGeq
  let rho : Real := (R - r) / 2
  have hrho : 0 < rho := by
    dsimp [rho]
    linarith
  let φseq : Nat -> ContDiffBump (0 : Point n) :=
    fun m => jensenMollifierBump n rho hrho m
  let gseq : Nat -> Point n -> Real :=
    fun m => (φseq m).normed volume ⋆[lsmul Real Real, volume] G
  refine ⟨gseq, ?_, ?_, ?_⟩
  · intro eps heps
    rcases exists_pos_forall_rOut_le_abs_normedBumpConvolution_sub_extension_le
        (n := n) (g := g) (G := G) hG (x0 := x0) (R := R) (r := r)
        hrR heps hGeq with
      ⟨η, hη_pos, hη⟩
    have htend :
        Filter.Tendsto (fun m : Nat => (φseq m).rOut) Filter.atTop (𝓝 0) := by
      simpa [φseq] using
        tendsto_jensenMollifierBump_rOut (n := n) rho hrho
    have hevent : ∀ᶠ m : Nat in Filter.atTop, (φseq m).rOut <= η := by
      filter_upwards [htend (Iio_mem_nhds hη_pos)] with m hm
      exact le_of_lt hm
    rcases Filter.eventually_atTop.1 hevent with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro m hm z hz
    exact hη (φseq m) (hN m hm) z hz
  · intro m
    exact contDiff_two_normedBumpConvolution_left (n := n) (φseq m) hG
  · intro m
    have hrho_le_margin : rho <= R - r := by
      dsimp [rho]
      linarith
    have hout_le_margin : (φseq m).rOut <= R - r :=
      le_trans
        (by
          simpa [φseq] using
            jensenMollifierBump_rOut_le_rho (n := n) rho hrho m)
        hrho_le_margin
    have hcontain : r + (φseq m).rOut <= R := by
      linarith
    exact convexOn_normedBumpConvolution_of_convexOn_extension
      (n := n) (φseq m) hG (x0 := x0) (R := R) (r := r)
      hconv hGeq hcontain

/--
Smooth convex approximation on interior closed balls, obtained by continuous
extension and mollification.
-/
theorem SmoothConvexApproximationOnInteriorClosedBallTheorem.proof :
    SmoothConvexApproximationOnInteriorClosedBallTheorem n :=
  SmoothConvexApproximationOnInteriorClosedBallTheorem.of_extensionMollification
    (n := n)
    (ContinuousExtensionConvexMollificationOnInteriorClosedBallTheorem.proof
      (n := n))

/--
The smooth approximation theorem needed for the mollification step in
Jensen's lemma.

In quantified mathematical form, this says: if `0 < r`, `r < R`,
`f : R^n -> R` is coordinate semiconvex on `closedBall x0 R` with
nonnegative constant `lambda`, and `f x < f x0` for every
`x ∈ closedBall x0 r` with `x ≠ x0`, then there are a number `gamma > 0` and
smooth functions `f_m : R^n -> R` such that:

* every boundary point of `closedBall x0 r` satisfies
  `f x ≤ f x0 - gamma`;
* `f_m -> f` uniformly on `closedBall x0 r`;
* every `f_m` is twice continuously differentiable;
* every `x ↦ f_m x + (lambda / 2) |x|^2` is convex on
  `closedBall x0 r`.

This is the exact mollification input from the source proof, separated from
the measure-theoretic and semijet arguments.
-/
def JensenSmoothConvexApproximationOnInteriorClosedBallTheorem (n : Nat) : Prop :=
  ∀ f : Point n -> Real,
    ∀ x0 : Point n,
    ∀ R r : Real, 0 < r -> r < R ->
      ∀ lambda : Real, 0 <= lambda ->
        CoordinateSemiconvexOn lambda (Metric.closedBall x0 R) f ->
          (∀ x : Point n, x ∈ Metric.closedBall x0 r -> x ≠ x0 -> f x < f x0) ->
            ∃ gamma : Real,
            ∃ fseq : Nat -> Point n -> Real,
              0 < gamma ∧
                (∀ x : Point n, x ∈ Metric.closedBall x0 r -> dist x x0 = r ->
                  f x <= f x0 - gamma) ∧
                (∀ eps : Real, 0 < eps ->
                  ∃ N : Nat, ∀ m : Nat, N <= m ->
                    ∀ z : Point n, z ∈ Metric.closedBall x0 r ->
                      |fseq m z - f z| <= eps) ∧
                (∀ m : Nat, ContDiff Real (2 : ℕ∞ω) (fseq m)) ∧
                (∀ m : Nat,
                  ConvexOn Real (Metric.closedBall x0 r)
                    (semiconvexConvexification lambda (fseq m)))

/--
Smooth convex approximation of the convexified function implies the smooth
semiconvex approximation theorem used in Jensen's lemma.

In quantified mathematical form, let
`g(x) = f(x) + (lambda / 2) |x|^2`. If `g` can be approximated uniformly on
`closedBall x0 r` by twice continuously differentiable functions `g_m` that
are convex on `closedBall x0 r`, then
`f_m(x) = g_m(x) - (lambda / 2) |x|^2` approximates `f`
uniformly on `closedBall x0 r`, each `f_m` is twice continuously
differentiable, and each
`x ↦ f_m(x) + (lambda / 2) |x|^2` is convex on `closedBall x0 r`.
-/
theorem JensenSmoothConvexApproximationOnInteriorClosedBallTheorem.of_smoothConvexApproximation
    (happrox : SmoothConvexApproximationOnInteriorClosedBallTheorem n) :
    JensenSmoothConvexApproximationOnInteriorClosedBallTheorem n := by
  intro f x0 R r hr hrR lambda hlambda hsemi hstrict
  have hboundaryStrict :
      ∀ x : Point n, x ∈ Metric.closedBall x0 r -> dist x x0 = r -> f x < f x0 := by
    intro x hx hdist
    exact hstrict x hx (fun hx0 => by
      subst x
      simp [dist_self] at hdist
      linarith)
  rcases exists_pos_boundary_gap_of_coordinateSemiconvexOn_larger_closedBall
      (n := n) (f := f) (x0 := x0) (r := r) (R := R)
      (lambda := lambda) hsemi hrR hboundaryStrict with
    ⟨gamma, hgamma, hgap⟩
  let g : Point n -> Real := semiconvexConvexification lambda f
  have hgconv : ConvexOn Real (Metric.closedBall x0 R) g :=
    hsemi.convexOn_semiconvexConvexification (convex_closedBall x0 R)
  rcases happrox g x0 R r hr hrR hgconv with
    ⟨gseq, hunif_g, hgseq_contDiff, hgseq_conv⟩
  let Q : Point n -> Real :=
    fun x => quadraticModel 0 0 0 (lambda • (1 : Hessian n)) x
  let fseq : Nat -> Point n -> Real := fun m x => gseq m x - Q x
  refine ⟨gamma, fseq, hgamma, hgap, ?_, ?_, ?_⟩
  · intro eps heps
    rcases hunif_g eps heps with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro m hm z hz
    have h := hN m hm z hz
    have hdiff :
        fseq m z - f z = gseq m z - g z := by
      simp [fseq, g, Q, semiconvexConvexification]
      ring
    simpa [hdiff] using h
  · intro m
    exact (hgseq_contDiff m).sub
      (contDiff_quadraticModel (n := n) (k := (2 : ℕ∞ω))
        0 0 0 (lambda • (1 : Hessian n)))
  · intro m
    exact (hgseq_conv m).congr fun x _hx => by
      simp [fseq, Q, semiconvexConvexification]

/--
It is enough to construct approximants which converge uniformly on the closed
ball and whose closed-ball global contact sets have a common positive lower
measure bound.

In quantified mathematical form, suppose that in the situation of
`JensenGlobalContactSetLimsupApproximationPrincipleOnClosedBall`, for every
`delta > 0` there are functions `f_m : R^n -> R` and a number `c > 0` such
that:

* for every `ε > 0`, there exists `N` such that, for every `m ≥ N` and every
  `y ∈ closedBall x0 r`, `|f_m(y) - f(y)| ≤ ε`;
* for every `m`, `JensenGlobalContactSet f_m x0 r (delta / 2)` is
  measurable;
* for every `m`, the measure of
  `JensenGlobalContactSet f_m x0 r (delta / 2)` is at least `c`.

Then the global-contact limsup approximation principle follows.
-/
theorem JensenGlobalContactSetLimsupApproximationPrincipleOnClosedBall.of_uniform_approximation
    (hdata :
      ∀ f : Point n -> Real,
      ∀ x0 : Point n,
      ∀ r : Real, 0 < r ->
        (∃ lambda : Real, CoordinateSemiconvexOn lambda (Metric.closedBall x0 r) f) ->
          (∀ x : Point n, x ∈ Metric.closedBall x0 r -> x ≠ x0 -> f x < f x0) ->
            ∀ delta : Real, 0 < delta ->
              ∃ fseq : Nat -> Point n -> Real,
              ∃ c : ℝ≥0∞,
                0 < c ∧
                  (∀ eps : Real, 0 < eps ->
                    ∃ N : Nat, ∀ m : Nat, N <= m ->
                      ∀ z : Point n, z ∈ Metric.closedBall x0 r ->
                        |fseq m z - f z| <= eps) ∧
                  (∀ m : Nat,
                    MeasurableSet (JensenGlobalContactSet (fseq m) x0 r (delta / 2))) ∧
                  (∀ m : Nat,
                    c <= volume (JensenGlobalContactSet (fseq m) x0 r (delta / 2)))) :
    JensenGlobalContactSetLimsupApproximationPrincipleOnClosedBall n := by
  intro f x0 r hr hsemi hstrict delta hdelta
  rcases hdata f x0 r hr hsemi hstrict delta hdelta with
    ⟨fseq, c, hc, hunif, hmeas, hlower⟩
  refine ⟨fseq, c, hc, hmeas, ?_, hlower⟩
  exact JensenGlobalContactSet.limsup_subset_jensenContactSet_of_uniformOn_closedBall
    (n := n) (fseq := fseq) (f := f) (x0 := x0) (r := r) (delta := delta)
    hdelta hunif

/--
It is enough to prove the uniform-approximation form of the global-contact
principle after discarding finitely many approximating functions.

In quantified mathematical form, suppose that in the situation of
`JensenGlobalContactSetLimsupApproximationPrincipleOnClosedBall`, for every
`delta > 0` there are a natural number `N`, functions `f_m : R^n -> R`, and a
number `c > 0` such that:

* for every `ε > 0`, there exists `M` such that, for every `m ≥ M` and every
  `y ∈ closedBall x0 r`, `|f_m(y) - f(y)| ≤ ε`;
* for every `m ≥ N`, `JensenGlobalContactSet f_m x0 r (delta / 2)` is
  measurable;
* for every `m ≥ N`, the measure of
  `JensenGlobalContactSet f_m x0 r (delta / 2)` is at least `c`.

Then the global-contact limsup approximation principle follows by replacing
`f_m` with the sequence `f_{N+m}`. This matches the source proof, where the
smooth estimates are required only for sufficiently small mollification
parameters, equivalently for sufficiently large integer indices.
-/
theorem
    JensenGlobalContactSetLimsupApproximationPrincipleOnClosedBall.of_uniform_approximation_tail
    (hdata :
      ∀ f : Point n -> Real,
      ∀ x0 : Point n,
      ∀ r : Real, 0 < r ->
        (∃ lambda : Real, CoordinateSemiconvexOn lambda (Metric.closedBall x0 r) f) ->
          (∀ x : Point n, x ∈ Metric.closedBall x0 r -> x ≠ x0 -> f x < f x0) ->
            ∀ delta : Real, 0 < delta ->
              ∃ N : Nat,
              ∃ fseq : Nat -> Point n -> Real,
              ∃ c : ℝ≥0∞,
                0 < c ∧
                  (∀ eps : Real, 0 < eps ->
                    ∃ M : Nat, ∀ m : Nat, M <= m ->
                      ∀ z : Point n, z ∈ Metric.closedBall x0 r ->
                        |fseq m z - f z| <= eps) ∧
                  (∀ m : Nat, N <= m ->
                    MeasurableSet (JensenGlobalContactSet (fseq m) x0 r (delta / 2))) ∧
                  (∀ m : Nat, N <= m ->
                    c <= volume (JensenGlobalContactSet (fseq m) x0 r (delta / 2)))) :
    JensenGlobalContactSetLimsupApproximationPrincipleOnClosedBall n := by
  refine
    JensenGlobalContactSetLimsupApproximationPrincipleOnClosedBall.of_uniform_approximation
      (n := n) ?_
  intro f x0 r hr hsemi hstrict delta hdelta
  rcases hdata f x0 r hr hsemi hstrict delta hdelta with
    ⟨N, fseq, c, hc, hunif, hmeas_tail, hlower_tail⟩
  refine ⟨fun m : Nat => fseq (N + m), c, hc, ?_, ?_, ?_⟩
  · intro eps heps
    rcases hunif eps heps with ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro m hm z hz
    exact hM (N + m) (le_trans hm (Nat.le_add_left m N)) z hz
  · intro m
    exact hmeas_tail (N + m) (Nat.le_add_right N m)
  · intro m
    exact hlower_tail (N + m) (Nat.le_add_right N m)

/--
The smooth approximation theorem implies the global-contact approximation
principle used to prove Jensen's lemma.

In quantified mathematical form, suppose `0 < r`, `r < R`, `f : R^n -> R`
is coordinate semiconvex on `closedBall x0 R`, and
`f x < f x0` for every `x ∈ closedBall x0 r` with `x ≠ x0`. If mollification
provides smooth functions `f_m` converging uniformly to `f` on
`closedBall x0 r` such that, for some nonnegative semiconvexity constant
`lambda`, every `x ↦ f_m x + (lambda / 2) |x|^2` is convex on
`closedBall x0 r`, then the smooth closed-ball contact-set estimate applies
to all sufficiently large `m`. Consequently the closed-ball global contact
sets for the functions `f_m` have a common positive lower measure bound, and
their limsup is contained in the Jensen contact set of `f`.
-/
theorem
    JensenGlobalContactSetInteriorLimsupApproximationPrincipleOnClosedBall.of_smooth_approximation
    (hsmooth : JensenSmoothConvexApproximationOnInteriorClosedBallTheorem n) :
    JensenGlobalContactSetInteriorLimsupApproximationPrincipleOnClosedBall n := by
  intro f x0 R r hr hrR hsemi hstrict delta hdelta
  rcases hsemi with ⟨lambda, hsemi_lambda⟩
  let mu : Real := max lambda 0
  have hmu_nonneg : 0 <= mu := by
    dsimp [mu]
    exact le_max_right _ _
  have hlambda_mu : lambda <= mu := by
    dsimp [mu]
    exact le_max_left _ _
  have hsemi_mu : CoordinateSemiconvexOn mu (Metric.closedBall x0 R) f :=
    hsemi_lambda.mono hlambda_mu
  rcases hsmooth f x0 R r hr hrR mu hmu_nonneg hsemi_mu hstrict with
    ⟨gamma, fseq, hgamma, hgap, hunif, hfseq, hconvseq⟩
  rcases
    exists_tail_measurable_common_lower_bound_jensenGlobalContactSet_of_uniformOn_convexified
      (n := n) (f := f) (fseq := fseq) (x0 := x0) (r := r)
      (delta := delta / 2) (gamma := gamma) (lambda := mu)
      (le_of_lt hr) (half_pos hdelta) hgamma hgap hunif hfseq hmu_nonneg hconvseq with
    ⟨N, c, hc, hmeas_tail, hlower_tail⟩
  refine ⟨fun m : Nat => fseq (N + m), c, hc, ?_, ?_, ?_⟩
  · intro m
    exact hmeas_tail (N + m) (Nat.le_add_right N m)
  · have hunif_shift :
        ∀ eps : Real, 0 < eps ->
          ∃ M : Nat, ∀ m : Nat, M <= m ->
            ∀ z : Point n, z ∈ Metric.closedBall x0 r ->
              |fseq (N + m) z - f z| <= eps := by
      intro eps heps
      rcases hunif eps heps with ⟨M, hM⟩
      refine ⟨M, ?_⟩
      intro m hm z hz
      exact hM (N + m) (le_trans hm (Nat.le_add_left m N)) z hz
    exact JensenGlobalContactSet.limsup_subset_jensenContactSet_of_uniformOn_closedBall
      (n := n) (fseq := fun m : Nat => fseq (N + m)) (f := f)
      (x0 := x0) (r := r) (delta := delta) hdelta hunif_shift
  · intro m
    exact hlower_tail (N + m) (Nat.le_add_right N m)

/--
It is enough to prove the approximation principle for all sufficiently large
indices.

In quantified mathematical form, suppose that in the situation of
`JensenContactSetLimsupApproximationPrincipleOnClosedBall`, for every
`delta > 0` there exist a sequence `f_m`, a natural number `N`, and a number
`c > 0` such that the measurability and common lower-measure bound for the
contact sets with perturbation radius `delta / 2` hold for every `m ≥ N`, and
the limsup of the full sequence is contained in the original contact set with
perturbation radius `delta`. Then the approximation principle follows by
replacing `f_m` with the shifted sequence `f_{N+m}`.
-/
theorem JensenContactSetLimsupApproximationPrincipleOnClosedBall.of_eventually
    (hdata :
      ∀ f : Point n -> Real,
      ∀ x0 : Point n,
      ∀ r : Real, 0 < r ->
        (∃ lambda : Real, CoordinateSemiconvexOn lambda (Metric.closedBall x0 r) f) ->
          (∀ x : Point n, x ∈ Metric.closedBall x0 r -> x ≠ x0 -> f x < f x0) ->
            ∀ delta : Real, 0 < delta ->
              ∃ N : Nat,
              ∃ fseq : Nat -> Point n -> Real,
              ∃ c : ℝ≥0∞,
                0 < c ∧
                  (∀ m : Nat, N <= m ->
                    MeasurableSet (JensenContactSet (fseq m) x0 r (delta / 2))) ∧
                  ((⋂ k : Nat, ⋃ m : Nat, ⋃ (_hm : k <= m),
                      JensenContactSet (fseq m) x0 r (delta / 2)) ⊆
                      JensenContactSet f x0 r delta) ∧
                  (∀ m : Nat, N <= m ->
                    c <= volume (JensenContactSet (fseq m) x0 r (delta / 2)))) :
    JensenContactSetLimsupApproximationPrincipleOnClosedBall n := by
  intro f x0 r hr hsemi hstrict delta hdelta
  rcases hdata f x0 r hr hsemi hstrict delta hdelta with
    ⟨N, fseq, c, hc, hmeas_tail, hlimsup_tail, hlower_tail⟩
  refine ⟨fun m : Nat => fseq (N + m), c, hc, ?_, ?_, ?_⟩
  · intro m
    exact hmeas_tail (N + m) (Nat.le_add_right N m)
  · intro x hx
    apply hlimsup_tail
    simp only [Set.mem_iInter, Set.mem_iUnion] at hx ⊢
    intro k
    rcases hx k with ⟨m, hkm, hmem⟩
    exact ⟨N + m, le_trans hkm (Nat.le_add_left m N), hmem⟩
  · intro m
    exact hlower_tail (N + m) (Nat.le_add_right N m)

/--
The nonsmooth approximation principle implies the localized Jensen contact-set
theorem.

In quantified mathematical form, if every strict closed-ball maximum satisfying
the coordinate semiconvexity hypothesis admits the approximating sequence and
uniform positive lower measure bound described in
`JensenContactSetLimsupApproximationPrincipleOnClosedBall`, then the Jensen
contact set has positive measure at every strict local maximum.
-/
theorem JensenContactSetPositiveMeasureOnClosedBallTheorem.of_limsup_approximation
    (happrox : JensenContactSetLimsupApproximationPrincipleOnClosedBall n) :
    JensenContactSetPositiveMeasureOnClosedBallTheorem n := by
  intro f x0 R hR hsemi hstrict delta hdelta
  rcases hstrict.exists_closedBall_strict hR with ⟨r, hr_pos, hr_le_R, hstrict_ball⟩
  rcases hsemi with ⟨lambda, hsemiR⟩
  have hsemi_r :
      ∃ lambda : Real, CoordinateSemiconvexOn lambda (Metric.closedBall x0 r) f :=
    ⟨lambda, hsemiR.mono_set (Metric.closedBall_subset_closedBall hr_le_R)⟩
  rcases happrox f x0 r hr_pos hsemi_r hstrict_ball delta hdelta with
    ⟨fseq, c, hc, hmeas, hlimsup, hlower⟩
  have hpos_r : 0 < volume (JensenContactSet f x0 r delta) := by
    refine measure_pos_of_limsup_subset_of_forall_measure_ge
      (μ := volume)
      (E := fun m : Nat => JensenContactSet (fseq m) x0 r (delta / 2))
      (B := Metric.closedBall x0 r)
      (K := JensenContactSet f x0 r delta)
      hc hmeas measure_closedBall_lt_top.ne ?_ hlimsup hlower
    intro m
    exact JensenContactSet.subset_closedBall (fseq m) x0 r (delta / 2)
  exact JensenContactSet.measure_pos_of_mono_radius hr_le_R hpos_r

/--
The global-contact approximation principle implies the localized Jensen
contact-set theorem.

In quantified mathematical form, if every strict closed-ball maximum
satisfying the coordinate semiconvexity hypothesis admits the approximating
sequence of closed-ball global contact sets and uniform positive lower
measure bound described in
`JensenGlobalContactSetLimsupApproximationPrincipleOnClosedBall`, then the
Jensen contact set has positive measure at every strict local maximum.
-/
theorem JensenContactSetPositiveMeasureOnClosedBallTheorem.of_global_limsup_approximation
    (happrox : JensenGlobalContactSetLimsupApproximationPrincipleOnClosedBall n) :
    JensenContactSetPositiveMeasureOnClosedBallTheorem n := by
  intro f x0 R hR hsemi hstrict delta hdelta
  rcases hstrict.exists_closedBall_strict hR with ⟨r, hr_pos, hr_le_R, hstrict_ball⟩
  rcases hsemi with ⟨lambda, hsemiR⟩
  have hsemi_r :
      ∃ lambda : Real, CoordinateSemiconvexOn lambda (Metric.closedBall x0 r) f :=
    ⟨lambda, hsemiR.mono_set (Metric.closedBall_subset_closedBall hr_le_R)⟩
  rcases happrox f x0 r hr_pos hsemi_r hstrict_ball delta hdelta with
    ⟨fseq, c, hc, hmeas, hlimsup, hlower⟩
  have hpos_r : 0 < volume (JensenContactSet f x0 r delta) := by
    refine measure_pos_of_limsup_subset_of_forall_measure_ge
      (μ := volume)
      (E := fun m : Nat => JensenGlobalContactSet (fseq m) x0 r (delta / 2))
      (B := Metric.closedBall x0 r)
      (K := JensenContactSet f x0 r delta)
      hc hmeas measure_closedBall_lt_top.ne ?_ hlimsup hlower
    intro m
    exact JensenGlobalContactSet.subset_closedBall (fseq m) x0 r (delta / 2)
  exact JensenContactSet.measure_pos_of_mono_radius hr_le_R hpos_r

/--
The source-aligned interior global-contact approximation principle implies
the localized Jensen contact-set theorem.

In quantified mathematical form, assume that the approximation principle is
available whenever the contact-set radius `r` is strictly smaller than a
radius `R` on which the function is semiconvex. If `f` is semiconvex on
`closedBall x0 R` and has a strict local maximum at `x0`, choose a positive
radius `r ≤ R / 2` on which the maximum is strict. Then `r < R`, so the
interior approximation principle gives approximating closed-ball global
contact sets on `closedBall x0 r` with a common positive lower measure bound.
The limsup measure lemma gives positive measure for
`JensenContactSet f x0 r delta`, and monotonicity in the radius gives
positive measure for `JensenContactSet f x0 R delta`.
-/
theorem JensenContactSetPositiveMeasureOnClosedBallTheorem.of_interior_global_limsup_approximation
    (happrox : JensenGlobalContactSetInteriorLimsupApproximationPrincipleOnClosedBall n) :
    JensenContactSetPositiveMeasureOnClosedBallTheorem n := by
  intro f x0 R hR hsemi hstrict delta hdelta
  have hR_half_pos : 0 < R / 2 := by linarith
  rcases hstrict.exists_closedBall_strict hR_half_pos with
    ⟨r, hr_pos, hr_le_half, hstrict_ball⟩
  have hr_lt_R : r < R := by linarith
  have hr_le_R : r <= R := by linarith
  rcases happrox f x0 R r hr_pos hr_lt_R hsemi hstrict_ball delta hdelta with
    ⟨fseq, c, hc, hmeas, hlimsup, hlower⟩
  have hpos_r : 0 < volume (JensenContactSet f x0 r delta) := by
    refine measure_pos_of_limsup_subset_of_forall_measure_ge
      (μ := volume)
      (E := fun m : Nat => JensenGlobalContactSet (fseq m) x0 r (delta / 2))
      (B := Metric.closedBall x0 r)
      (K := JensenContactSet f x0 r delta)
      hc hmeas measure_closedBall_lt_top.ne ?_ hlimsup hlower
    intro m
    exact JensenGlobalContactSet.subset_closedBall (fseq m) x0 r (delta / 2)
  exact JensenContactSet.measure_pos_of_mono_radius hr_le_R hpos_r

/--
Smooth convex approximation on interior closed balls implies the localized
Jensen contact-set theorem.

In quantified mathematical form, assume that every convex function on a closed
ball `closedBall x0 R` can be uniformly approximated on each smaller closed
ball `closedBall x0 r`, with `0 < r < R`, by twice continuously
differentiable functions which are convex on `closedBall x0 r`. Then Jensen's
contact set has positive Lebesgue measure for every semiconvex function with a
strict local maximum.
-/
theorem JensenContactSetPositiveMeasureOnClosedBallTheorem.of_smoothConvexApproximation
    (happrox : SmoothConvexApproximationOnInteriorClosedBallTheorem n) :
    JensenContactSetPositiveMeasureOnClosedBallTheorem n :=
  JensenContactSetPositiveMeasureOnClosedBallTheorem.of_interior_global_limsup_approximation
    (n := n)
    (JensenGlobalContactSetInteriorLimsupApproximationPrincipleOnClosedBall.of_smooth_approximation
        (n := n)
        (JensenSmoothConvexApproximationOnInteriorClosedBallTheorem.of_smoothConvexApproximation
          (n := n) happrox))

/--
The localized Jensen contact-set theorem for semiconvex functions.

In quantified mathematical form, if `f : R^n -> R` is semiconvex in a
neighborhood of a strict local maximum point `x0`, then for every `delta > 0`
the set of points where some linear perturbation with slope of norm less than
`delta` has a local maximum has positive Lebesgue measure.
-/
theorem JensenContactSetPositiveMeasureOnClosedBallTheorem.proof :
    JensenContactSetPositiveMeasureOnClosedBallTheorem n :=
  JensenContactSetPositiveMeasureOnClosedBallTheorem.of_smoothConvexApproximation
    (n := n)
    (SmoothConvexApproximationOnInteriorClosedBallTheorem.proof (n := n))

/--
It suffices to prove the localized Jensen contact-set theorem for closed balls
on which the center is strictly larger than every other point.

In quantified mathematical form, suppose that the following statement has been
proved: for every `f`, `x0`, and `r > 0`, if `f` is coordinate semiconvex on
`closedBall x0 r` and `f x < f x0` for every
`x ∈ closedBall x0 r` with `x ≠ x0`, then
`JensenContactSet f x0 r δ` has positive measure for every `δ > 0`.
Then the full localized Jensen contact-set theorem follows for every strict
local maximum point.
-/
theorem JensenContactSetPositiveMeasureOnClosedBallTheorem.of_forall_closedBall_strict
    (hsmall :
      ∀ f : Point n -> Real,
      ∀ x0 : Point n,
      ∀ r : Real, 0 < r ->
        (∃ lambda : Real, CoordinateSemiconvexOn lambda (Metric.closedBall x0 r) f) ->
          (∀ x : Point n, x ∈ Metric.closedBall x0 r -> x ≠ x0 -> f x < f x0) ->
            ∀ delta : Real, 0 < delta ->
              0 < volume (JensenContactSet f x0 r delta)) :
    JensenContactSetPositiveMeasureOnClosedBallTheorem n := by
  intro f x0 R hR hsemi hstrict delta hdelta
  rcases hstrict.exists_closedBall_strict hR with ⟨r, hr_pos, hr_le_R, hstrict_ball⟩
  rcases hsemi with ⟨lambda, hsemiR⟩
  have hsemi_r :
      ∃ lambda : Real, CoordinateSemiconvexOn lambda (Metric.closedBall x0 r) f :=
    ⟨lambda, hsemiR.mono_set (Metric.closedBall_subset_closedBall hr_le_R)⟩
  exact JensenContactSet.measure_pos_of_mono_radius hr_le_R
    (hsmall f x0 r hr_pos hsemi_r hstrict_ball delta hdelta)

end ViscositySolns
