/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Analysis.SemiconvexJensen.Aleksandrov.JetCalculus.Basic

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Core Aleksandrov Theorem Statements
-/

@[expose] public noncomputable section

open scoped ContDiff MatrixOrder Topology
open scoped ENNReal

open ContinuousLinearMap MeasureTheory

namespace ViscositySolns

variable {n : Nat}

variable {n : Nat}

/--
Aleksandrov's theorem in the jet-based form needed by the proof of Jensen's
matrix lemma.

In quantified mathematical form, this says: if `f : R^n -> R` is semiconvex,
then the set of points at which `f` has no second-order jet has Lebesgue
measure zero.
-/
def AleksandrovSecondDifferentiabilityByJetsTheorem (n : Nat) : Prop :=
  ∀ f : Point n -> Real,
    (∃ lambda : Real, CoordinateSemiconvexOn lambda Set.univ f) ->
      volume {x : Point n | ¬ HasSomeSecondOrderJet f x} = 0

/--
Global Aleksandrov theorem for convex functions.

This is the direct global form of the Mignot proof before the local closed-ball
and semiconvex reductions.
-/
def AleksandrovSecondDifferentiabilityByJetsForConvexTheorem (n : Nat) :
    Prop :=
  ∀ f : Point n -> Real,
    ConvexOn Real Set.univ f ->
      volume {x : Point n | ¬ HasSomeSecondOrderJet f x} = 0

/--
If a set is null on every closed ball centered at the origin with radius
`k + 1`, then it is null on all of coordinate space.
-/
theorem volume_eq_zero_of_closedBall_add_one_inter_eq_zero
    {s : Set (Point n)}
    (hnull :
      ∀ k : Nat,
        volume (Metric.closedBall (0 : Point n) ((k : Real) + 1) ∩ s) = 0) :
    volume s = 0 := by
  have hcover :
      s ⊆ ⋃ k : Nat, Metric.closedBall (0 : Point n) ((k : Real) + 1) ∩ s := by
    intro x hx
    have hxcover : x ∈ ⋃ k : Nat, Metric.closedBall (0 : Point n) k := by
      rw [Metric.iUnion_closedBall_nat (0 : Point n)]
      trivial
    rcases Set.mem_iUnion.mp hxcover with ⟨k, hxk⟩
    refine Set.mem_iUnion.mpr ⟨k, ?_, hx⟩
    exact Metric.closedBall_subset_closedBall (by norm_num) hxk
  exact measure_mono_null hcover (measure_iUnion_null hnull)

/--
Localized Aleksandrov second-differentiability theorem on a closed ball.

In quantified mathematical form, this says: if `f : R^n -> R` is coordinate
semiconvex on `closedBall x0 r` and `0 < r`, then the set of points in
`closedBall x0 r` at which `f` has no second-order jet has Lebesgue measure
zero.
-/
def AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem (n : Nat) : Prop :=
  ∀ f : Point n -> Real,
    ∀ x0 : Point n,
    ∀ r : Real, 0 < r ->
      (∃ lambda : Real, CoordinateSemiconvexOn lambda (Metric.closedBall x0 r) f) ->
        volume (Metric.closedBall x0 r ∩
          {x : Point n | ¬ HasSomeSecondOrderJet f x}) = 0

/--
Local semiconvex functions on closed balls admit globally semiconvex
representatives on the corresponding open balls.
-/
def CoordinateSemiconvexClosedBallExtensionHypothesis (n : Nat) : Prop :=
  ∀ f : Point n -> Real,
    ∀ x0 : Point n,
    ∀ r : Real, 0 < r ->
      (∃ lambda : Real,
        CoordinateSemiconvexOn lambda (Metric.closedBall x0 r) f) ->
        ∃ g : Point n -> Real,
          (∃ lambda : Real,
            CoordinateSemiconvexOn lambda Set.univ g) ∧
            Set.EqOn g f (Metric.ball x0 r)

/--
Interior version of the local/global semiconvex bridge.

The extension is only required on a smaller open ball `ball x0 r` whose radius
is strictly below the radius `R` on which semiconvexity is known.
-/
def CoordinateSemiconvexInteriorClosedBallExtensionHypothesis (n : Nat) :
    Prop :=
  ∀ f : Point n -> Real,
    ∀ x0 : Point n,
    ∀ R r : Real, 0 < r -> r < R ->
      (∃ lambda : Real,
        CoordinateSemiconvexOn lambda (Metric.closedBall x0 R) f) ->
        ∃ g : Point n -> Real,
          (∃ lambda : Real,
            CoordinateSemiconvexOn lambda Set.univ g) ∧
            Set.EqOn g f (Metric.ball x0 r)

/--
The open ball is covered by the countable exhaustion of closed balls with
radii `R - R / (k + 2)`.
-/
theorem ball_subset_iUnion_closedBall_shrink
    (x0 : Point n) {R : Real} (hR : 0 < R) :
    Metric.ball x0 R ⊆
      ⋃ k : Nat, Metric.closedBall x0 (R - R / ((k : Real) + 2)) := by
  intro x hx
  rw [Metric.mem_ball] at hx
  let eps : Real := R - dist x x0
  have heps_pos : 0 < eps := by
    dsimp [eps]
    simpa [dist_comm] using sub_pos.mpr hx
  have hratio_pos : 0 < eps / R := div_pos heps_pos hR
  rcases exists_nat_one_div_lt hratio_pos with ⟨k, hk⟩
  refine Set.mem_iUnion.mpr ⟨k, ?_⟩
  rw [Metric.mem_closedBall]
  have hden1_pos : 0 < (k : Real) + 1 := by positivity
  have hden2_pos : 0 < (k : Real) + 2 := by positivity
  have hden_le : (k : Real) + 1 <= (k : Real) + 2 := by linarith
  have hrecip_le :
      (1 : Real) / ((k : Real) + 2) <=
        (1 : Real) / ((k : Real) + 1) :=
    one_div_le_one_div_of_le hden1_pos hden_le
  have hrecip_lt : (1 : Real) / ((k : Real) + 2) < eps / R :=
    lt_of_le_of_lt hrecip_le hk
  have hRdiv_lt : R / ((k : Real) + 2) < eps := by
    calc
      R / ((k : Real) + 2) =
          R * ((1 : Real) / ((k : Real) + 2)) := by ring
      _ < R * (eps / R) := mul_lt_mul_of_pos_left hrecip_lt hR
      _ = eps := by field_simp [hR.ne']
  dsimp [eps] at hRdiv_lt
  have hdist_le : dist x x0 <= R - R / ((k : Real) + 2) := by
    linarith
  simpa [dist_comm] using hdist_le

/--
A metric sphere in coordinate space has zero Lebesgue measure as soon as the
radius is positive.
-/
theorem volume_sphere_eq_zero_of_pos (x0 : Point n) {r : Real} (hr : 0 < r) :
    volume (Metric.sphere x0 r) = 0 := by
  simpa using
    (MeasureTheory.Measure.addHaar_sphere_of_ne_zero
      (volume : Measure (Point n)) x0 hr.ne')

/--
To prove a bad set is null on a closed ball, it suffices to prove it is null
on the corresponding open ball: the boundary sphere is null.
-/
theorem volume_closedBall_inter_eq_zero_of_ball_inter_eq_zero
    {s : Set (Point n)} {x0 : Point n} {r : Real} (hr : 0 < r)
    (hball : volume (Metric.ball x0 r ∩ s) = 0) :
    volume (Metric.closedBall x0 r ∩ s) = 0 := by
  have hsphere :
      volume (Metric.sphere x0 r ∩ s) = 0 :=
    measure_mono_null Set.inter_subset_left
      (volume_sphere_eq_zero_of_pos x0 hr)
  refine measure_mono_null ?_ (measure_union_null hball hsphere)
  rintro x ⟨hxclosed, hxs⟩
  by_cases hxball : x ∈ Metric.ball x0 r
  · exact Or.inl ⟨hxball, hxs⟩
  · have hxsphere : x ∈ Metric.sphere x0 r := by
      rw [Metric.mem_sphere]
      rw [Metric.mem_closedBall] at hxclosed
      rw [Metric.mem_ball] at hxball
      exact le_antisymm hxclosed (le_of_not_gt hxball)
    exact Or.inr ⟨hxsphere, hxs⟩

/--
Open-ball version of localized Aleksandrov implies the closed-ball statement.

This isolates the boundary-null reduction needed to pass from arguments on the
interior of a ball to the closed-ball theorem consumed by Jensen's lemma.
-/
theorem AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.of_openBall
    (hAleksandrov :
      ∀ f : Point n -> Real,
        ∀ x0 : Point n,
        ∀ r : Real, 0 < r ->
          (∃ lambda : Real, CoordinateSemiconvexOn lambda
            (Metric.closedBall x0 r) f) ->
            volume (Metric.ball x0 r ∩
              {x : Point n | ¬ HasSomeSecondOrderJet f x}) = 0) :
    AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem n := by
  intro f x0 r hr hsemi
  exact volume_closedBall_inter_eq_zero_of_ball_inter_eq_zero hr
    (hAleksandrov f x0 r hr hsemi)

/--
The global semiconvex Aleksandrov theorem implies the local closed-ball theorem,
provided each locally semiconvex function has a globally semiconvex
representative agreeing with it on the open ball.

This is the semiconvex local/global bridge for the source proof: ordinary jets
are local, and the closed-ball boundary has zero measure.
-/
theorem AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.of_global
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsTheorem n)
    (hext : CoordinateSemiconvexClosedBallExtensionHypothesis n) :
    AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem n := by
  apply AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.of_openBall
  intro f x0 r hr hsemi
  rcases hext f x0 r hr hsemi with ⟨g, hgsemi, hgf⟩
  refine measure_mono_null ?_ (hAleksandrov g hgsemi)
  rintro x ⟨hxball, hxnoJet⟩ hxgJet
  have hgf_nhds : g =ᶠ[𝓝 x] f := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hxball] with y hy
    exact hgf hy
  exact hxnoJet (hxgJet.congr_of_eventuallyEq hgf_nhds)

/--
Named-hypothesis version of the global-to-local semiconvex bridge.
-/
theorem AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.of_global_extension
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsTheorem n)
    (hext : CoordinateSemiconvexClosedBallExtensionHypothesis n) :
    AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem n :=
  AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.of_global
    hAleksandrov hext

/--
The global semiconvex Aleksandrov theorem implies the local closed-ball theorem
from the interior local/global extension bridge.

This avoids requiring an extension all the way up to the boundary of the
original closed ball: the open ball is exhausted by smaller closed balls, and
the boundary sphere is null.
-/
theorem AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.of_global_interiorExtension
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsTheorem n)
    (hext : CoordinateSemiconvexInteriorClosedBallExtensionHypothesis n) :
    AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem n := by
  apply AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.of_openBall
  intro f x0 R hR hsemi
  let bad : Set (Point n) := {x : Point n | ¬ HasSomeSecondOrderJet f x}
  have hcover :
      Metric.ball x0 R ∩ bad ⊆
        ⋃ k : Nat,
          Metric.closedBall x0 (R - R / ((k : Real) + 2)) ∩ bad := by
    rintro x ⟨hxball, hxbad⟩
    have hxcover :
        x ∈ ⋃ k : Nat,
          Metric.closedBall x0 (R - R / ((k : Real) + 2)) :=
      ball_subset_iUnion_closedBall_shrink (n := n) x0 hR hxball
    rcases Set.mem_iUnion.mp hxcover with
      ⟨k, hxk⟩
    exact Set.mem_iUnion.mpr ⟨k, ⟨hxk, hxbad⟩⟩
  refine measure_mono_null hcover (measure_iUnion_null ?_)
  intro k
  let rk : Real := R - R / ((k : Real) + 2)
  let sk : Real := R - R / ((k : Real) + 3)
  have hden2_pos : 0 < (k : Real) + 2 := by positivity
  have hden3_pos : 0 < (k : Real) + 3 := by positivity
  have hrecip2_pos : 0 < R / ((k : Real) + 2) := div_pos hR hden2_pos
  have hrecip3_pos : 0 < R / ((k : Real) + 3) := div_pos hR hden3_pos
  have hden23 : (k : Real) + 2 <= (k : Real) + 3 := by linarith
  have hrecip_le :
      (1 : Real) / ((k : Real) + 3) <=
        (1 : Real) / ((k : Real) + 2) :=
    one_div_le_one_div_of_le hden2_pos hden23
  have hRdiv_le :
      R / ((k : Real) + 3) <= R / ((k : Real) + 2) := by
    calc
      R / ((k : Real) + 3) =
          R * ((1 : Real) / ((k : Real) + 3)) := by ring
      _ <= R * ((1 : Real) / ((k : Real) + 2)) :=
          mul_le_mul_of_nonneg_left hrecip_le hR.le
      _ = R / ((k : Real) + 2) := by ring
  have hrk_lt_sk : rk < sk := by
    dsimp [rk, sk]
    have hstrict :
        R / ((k : Real) + 3) < R / ((k : Real) + 2) := by
      have hden23_strict : (k : Real) + 2 < (k : Real) + 3 := by linarith
      have hrecip_strict :
          (1 : Real) / ((k : Real) + 3) <
            (1 : Real) / ((k : Real) + 2) :=
        one_div_lt_one_div_of_lt hden2_pos hden23_strict
      calc
        R / ((k : Real) + 3) =
            R * ((1 : Real) / ((k : Real) + 3)) := by ring
        _ < R * ((1 : Real) / ((k : Real) + 2)) :=
            mul_lt_mul_of_pos_left hrecip_strict hR
        _ = R / ((k : Real) + 2) := by ring
    linarith
  have hsk_pos : 0 < sk := by
    dsimp [sk]
    have hlt : R / ((k : Real) + 3) < R := by
      have hden_gt_one : (1 : Real) < (k : Real) + 3 := by
        have hk_nonneg : 0 <= (k : Real) := Nat.cast_nonneg k
        linarith
      rw [div_lt_iff₀ hden3_pos]
      nlinarith
    linarith
  have hsk_lt_R : sk < R := by
    dsimp [sk]
    linarith
  rcases hext f x0 R sk hsk_pos hsk_lt_R hsemi with
    ⟨g, hgsemi, hgf⟩
  refine measure_mono_null ?_ (hAleksandrov g hgsemi)
  rintro x ⟨hxrk, hxnoJet⟩ hxgJet
  have hxsk : x ∈ Metric.ball x0 sk :=
    Metric.closedBall_subset_ball hrk_lt_sk hxrk
  have hgf_nhds : g =ᶠ[𝓝 x] f := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hxsk] with y hy
    exact hgf hy
  exact hxnoJet (hxgJet.congr_of_eventuallyEq hgf_nhds)

/--
The global convex Aleksandrov theorem implies the global semiconvex
Aleksandrov theorem by adding the convexifying quadratic.
-/
theorem AleksandrovSecondDifferentiabilityByJetsForConvexTheorem.to_semiconvex
    (hAleksandrov :
      AleksandrovSecondDifferentiabilityByJetsForConvexTheorem n) :
    AleksandrovSecondDifferentiabilityByJetsTheorem n := by
  intro f hsemi
  rcases hsemi with ⟨lambda, hsemi⟩
  refine measure_mono_null ?_
    (hAleksandrov (semiconvexConvexification lambda f) ?_)
  · intro x hxnoJet hconvJet
    exact hxnoJet
      (HasSomeSecondOrderJet.of_semiconvexConvexification
        (lambda := lambda) hconvJet)
  · exact hsemi.convexOn_semiconvexConvexification convex_univ

/--
The localized closed-ball semiconvex Aleksandrov theorem implies the global
semiconvex Aleksandrov theorem by covering coordinate space with closed balls.
-/
theorem AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.to_global
    (hAleksandrov :
      AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem n) :
    AleksandrovSecondDifferentiabilityByJetsTheorem n := by
  intro f hsemi
  rcases hsemi with ⟨lambda, hsemi⟩
  apply volume_eq_zero_of_closedBall_add_one_inter_eq_zero
  intro k
  have hkpos : 0 < (k : Real) + 1 := by positivity
  exact hAleksandrov f (0 : Point n) ((k : Real) + 1) hkpos
    ⟨lambda, hsemi.mono_set (by intro x _hx; trivial)⟩

/--
The global convex source-proof theorem implies the local closed-ball
semiconvex theorem whenever local semiconvex functions admit globally
semiconvex representatives on the open ball.
-/
theorem AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.of_global_convex_semiconvex
    (hAleksandrov :
      AleksandrovSecondDifferentiabilityByJetsForConvexTheorem n)
    (hext : CoordinateSemiconvexClosedBallExtensionHypothesis n) :
    AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem n :=
  AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.of_global
    hAleksandrov.to_semiconvex hext

/--
Localized Aleksandrov second-differentiability theorem for convex functions on
a closed ball.

This is the convex target produced by the source proof after reducing a
semiconvex function to its convexification.
-/
def AleksandrovSecondDifferentiabilityByJetsForConvexOnClosedBallTheorem
    (n : Nat) : Prop :=
  ∀ f : Point n -> Real,
    ∀ x0 : Point n,
    ∀ r : Real, 0 < r ->
      ConvexOn Real (Metric.closedBall x0 r) f ->
        volume (Metric.closedBall x0 r ∩
          {x : Point n | ¬ HasSomeSecondOrderJet f x}) = 0

/--
Local convex functions on closed balls admit globally convex representatives on
the corresponding open balls.
-/
def ConvexClosedBallExtensionHypothesis (n : Nat) : Prop :=
  ∀ f : Point n -> Real,
    ∀ x0 : Point n,
    ∀ r : Real, 0 < r ->
      ConvexOn Real (Metric.closedBall x0 r) f ->
        ∃ g : Point n -> Real,
          ConvexOn Real Set.univ g ∧
            Set.EqOn g f (Metric.ball x0 r)

/--
Interior version of the convex local/global bridge.

The globally convex representative is only required to agree with the local
convex function on a smaller open ball.
-/
def ConvexInteriorClosedBallExtensionHypothesis (n : Nat) : Prop :=
  ∀ f : Point n -> Real,
    ∀ x0 : Point n,
    ∀ R r : Real, 0 < r -> r < R ->
      ConvexOn Real (Metric.closedBall x0 R) f ->
        ∃ g : Point n -> Real,
          ConvexOn Real Set.univ g ∧
            Set.EqOn g f (Metric.ball x0 r)

/--
A convex closed-ball extension theorem implies the corresponding semiconvex
closed-ball extension theorem by extending the convexification and subtracting
the same quadratic globally.
-/
theorem ConvexClosedBallExtensionHypothesis.to_coordinateSemiconvex
    (hext : ConvexClosedBallExtensionHypothesis n) :
    CoordinateSemiconvexClosedBallExtensionHypothesis n := by
  intro f x0 r hr hsemi
  rcases hsemi with ⟨lambda, hsemi⟩
  let q : Point n -> Real := semiconvexConvexification lambda f
  have hqconv : ConvexOn Real (Metric.closedBall x0 r) q :=
    hsemi.convexOn_semiconvexConvexification (convex_closedBall x0 r)
  rcases hext q x0 r hr hqconv with ⟨G, hGconv, hGq⟩
  let g : Point n -> Real :=
    fun x => G x - quadraticModel 0 0 0 (lambda • (1 : Hessian n)) x
  refine ⟨g, ⟨lambda, ?_⟩, ?_⟩
  · have hconv :
        ConvexOn Real Set.univ (semiconvexConvexification lambda g) :=
      hGconv.congr fun x _hx => by
        simp [g, semiconvexConvexification]
    exact ConvexOn.coordinateSemiconvexOn_of_semiconvexConvexification hconv
  · intro x hx
    have hxG := hGq hx
    simp [g, q, semiconvexConvexification, hxG]

/--
A convex interior closed-ball extension theorem implies the corresponding
semiconvex interior extension theorem by extending the convexification and
subtracting the same quadratic globally.
-/
theorem ConvexInteriorClosedBallExtensionHypothesis.to_coordinateSemiconvex
    (hext : ConvexInteriorClosedBallExtensionHypothesis n) :
    CoordinateSemiconvexInteriorClosedBallExtensionHypothesis n := by
  intro f x0 R r hr hrR hsemi
  rcases hsemi with ⟨lambda, hsemi⟩
  let q : Point n -> Real := semiconvexConvexification lambda f
  have hqconv : ConvexOn Real (Metric.closedBall x0 R) q :=
    hsemi.convexOn_semiconvexConvexification (convex_closedBall x0 R)
  rcases hext q x0 R r hr hrR hqconv with ⟨G, hGconv, hGq⟩
  let g : Point n -> Real :=
    fun x => G x - quadraticModel 0 0 0 (lambda • (1 : Hessian n)) x
  refine ⟨g, ⟨lambda, ?_⟩, ?_⟩
  · have hconv :
        ConvexOn Real Set.univ (semiconvexConvexification lambda g) :=
      hGconv.congr fun x _hx => by
        simp [g, semiconvexConvexification]
    exact ConvexOn.coordinateSemiconvexOn_of_semiconvexConvexification hconv
  · intro x hx
    have hxG := hGq hx
    simp [g, q, semiconvexConvexification, hxG]

/--
The global semiconvex Aleksandrov theorem implies the local closed-ball theorem
from the more primitive convex extension bridge.
-/
theorem AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.of_global_convexExtension
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsTheorem n)
    (hext : ConvexClosedBallExtensionHypothesis n) :
    AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem n :=
  AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.of_global
    hAleksandrov hext.to_coordinateSemiconvex

/--
The global semiconvex Aleksandrov theorem implies the local closed-ball theorem
from the more primitive convex interior extension bridge.
-/
theorem
    AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.of_global_convexInteriorExtension
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsTheorem n)
    (hext : ConvexInteriorClosedBallExtensionHypothesis n) :
    AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem n :=
  AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.of_global_interiorExtension
    hAleksandrov hext.to_coordinateSemiconvex

/--
The global convex Aleksandrov theorem implies the local closed-ball theorem from
the convex interior extension bridge.
-/
theorem
    AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.of_global_convexInterior
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsForConvexTheorem n)
    (hext : ConvexInteriorClosedBallExtensionHypothesis n) :
    AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem n :=
  AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.of_global_convexInteriorExtension
    hAleksandrov.to_semiconvex hext

/--
Open-ball version of the convex localized Aleksandrov theorem implies the
closed-ball convex statement.
-/
theorem AleksandrovSecondDifferentiabilityByJetsForConvexOnClosedBallTheorem.of_openBall
    (hAleksandrov :
      ∀ f : Point n -> Real,
        ∀ x0 : Point n,
        ∀ r : Real, 0 < r ->
          ConvexOn Real (Metric.closedBall x0 r) f ->
            volume (Metric.ball x0 r ∩
              {x : Point n | ¬ HasSomeSecondOrderJet f x}) = 0) :
    AleksandrovSecondDifferentiabilityByJetsForConvexOnClosedBallTheorem n := by
  intro f x0 r hr hconv
  exact volume_closedBall_inter_eq_zero_of_ball_inter_eq_zero hr
    (hAleksandrov f x0 r hr hconv)

/--
The convex localized Aleksandrov theorem implies the semiconvex localized
Aleksandrov theorem by adding the convexifying quadratic.
-/
theorem AleksandrovSecondDifferentiabilityByJetsForConvexOnClosedBallTheorem.to_semiconvex
    (hAleksandrov :
      AleksandrovSecondDifferentiabilityByJetsForConvexOnClosedBallTheorem n) :
    AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem n := by
  intro f x0 r hr hsemi
  rcases hsemi with ⟨lambda, hsemi⟩
  refine
    measure_mono_null ?_
      (hAleksandrov (semiconvexConvexification lambda f) x0 r hr ?_)
  · rintro x ⟨hxball, hxnoJet⟩
    refine ⟨hxball, ?_⟩
    intro hconvJet
    exact hxnoJet
      (HasSomeSecondOrderJet.of_semiconvexConvexification
        (lambda := lambda) hconvJet)
  · exact
      hsemi.convexOn_semiconvexConvexification
        (convex_closedBall x0 r)

/--
An open-ball convex Aleksandrov theorem implies the closed-ball semiconvex
Aleksandrov theorem.

This composes two local reductions: the boundary sphere is null, and
semiconvexity becomes convexity after adding the standard quadratic.
-/
theorem AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.of_convex_openBall
    (hAleksandrov :
      ∀ g : Point n -> Real,
        ∀ x0 : Point n,
        ∀ r : Real, 0 < r ->
          ConvexOn Real (Metric.closedBall x0 r) g ->
            volume (Metric.ball x0 r ∩
              {x : Point n | ¬ HasSomeSecondOrderJet g x}) = 0) :
    AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem n := by
  apply AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.of_openBall
  intro f x0 r hr hsemi
  rcases hsemi with ⟨lambda, hsemi⟩
  refine measure_mono_null ?_ (hAleksandrov
    (semiconvexConvexification lambda f) x0 r hr ?_)
  · rintro x ⟨hxball, hxnoJet⟩
    refine ⟨hxball, ?_⟩
    intro hconvJet
    exact hxnoJet
      (HasSomeSecondOrderJet.of_semiconvexConvexification
        (lambda := lambda) hconvJet)
  · exact
      hsemi.convexOn_semiconvexConvexification
        (convex_closedBall x0 r)

local notation "AleksJetsForConvexClosedBall" =>
  AleksandrovSecondDifferentiabilityByJetsForConvexOnClosedBallTheorem

namespace AleksandrovSecondDifferentiabilityByJetsForConvexOnClosedBallTheorem

/--
The localized convex closed-ball theorem implies the global convex theorem by
covering coordinate space with the closed balls `closedBall 0 (k + 1)`.
-/
theorem to_global
    (hAleksandrov : AleksJetsForConvexClosedBall n) :
    AleksandrovSecondDifferentiabilityByJetsForConvexTheorem n := by
  intro f hconv
  apply volume_eq_zero_of_closedBall_add_one_inter_eq_zero
  intro k
  have hkpos : 0 < (k : Real) + 1 := by positivity
  have hconvBall :
      ConvexOn Real (Metric.closedBall (0 : Point n) ((k : Real) + 1)) f := by
    exact
      ⟨convex_closedBall (0 : Point n) ((k : Real) + 1), fun x hx y hy a b ha hb hab =>
        hconv.2 trivial trivial ha hb hab⟩
  exact hAleksandrov f (0 : Point n) ((k : Real) + 1) hkpos hconvBall

/--
The global convex Aleksandrov theorem implies the local closed-ball convex
theorem, provided each closed-ball convex function has a globally convex
representative agreeing with it on the open ball.

This is the formal local/global bridge for the source proof: ordinary jets are
local, and the boundary sphere of the closed ball is null.
-/
theorem of_global
    (hAleksandrov :
      AleksandrovSecondDifferentiabilityByJetsForConvexTheorem n)
    (hext : ConvexClosedBallExtensionHypothesis n) :
    AleksJetsForConvexClosedBall n := by
  apply of_openBall
  intro f x0 r hr hconv
  rcases hext f x0 r hr hconv with ⟨g, hgconv, hgf⟩
  refine measure_mono_null ?_ (hAleksandrov g hgconv)
  rintro x ⟨hxball, hxnoJet⟩ hxgJet
  have hgf_nhds : g =ᶠ[𝓝 x] f := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hxball] with y hy
    exact hgf hy
  exact hxnoJet (hxgJet.congr_of_eventuallyEq hgf_nhds)

/--
Named-hypothesis version of the global-to-local convex bridge.
-/
theorem of_global_extension
    (hAleksandrov :
      AleksandrovSecondDifferentiabilityByJetsForConvexTheorem n)
    (hext : ConvexClosedBallExtensionHypothesis n) :
    AleksJetsForConvexClosedBall n :=
  of_global hAleksandrov hext

end AleksandrovSecondDifferentiabilityByJetsForConvexOnClosedBallTheorem

/--
The global convex source-proof theorem, plus a local globally convex
representative on open balls, implies the closed-ball semiconvex Aleksandrov
theorem.
-/
theorem AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.of_global_convex
    (hAleksandrov :
      AleksandrovSecondDifferentiabilityByJetsForConvexTheorem n)
    (hext : ConvexClosedBallExtensionHypothesis n) :
    AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem n := by
  let T := AleksandrovSecondDifferentiabilityByJetsForConvexOnClosedBallTheorem n
  have hconv : T := by
    exact
      AleksandrovSecondDifferentiabilityByJetsForConvexOnClosedBallTheorem.of_global
        hAleksandrov hext
  exact hconv.to_semiconvex

end ViscositySolns
