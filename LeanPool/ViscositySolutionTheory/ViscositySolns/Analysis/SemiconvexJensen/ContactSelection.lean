/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Analysis.SemiconvexJensen.Jensen

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Aleksandrov--Jensen theorem for semiconvex functions (ContactSelection)

Part of the Aleksandrov--Jensen development assembling the localized Jensen
contact-set theorem with Aleksandrov differentiability. Split from
`SemiconvexJensen.lean`; see the umbrella module docstring.
-/
@[expose] public noncomputable section

open scoped ContDiff MatrixOrder Topology
open scoped Convolution
open scoped ENNReal

open ContinuousLinearMap MeasureTheory

namespace ViscositySolns

variable {n : Nat}
/--
Jensen's lemma for semiconvex functions, stated as the contact-set theorem
from the source paper.

In quantified mathematical form, if `f : R^n -> R` is semiconvex and `x0` is
a strict local maximum point of `f`, then for every `r > 0` and every
`delta > 0`, the set of points `x ∈ B(x0, r)` for which there exists
`p ∈ B(0, delta)` such that `y ↦ f y + p · y` has a local maximum at `x`
has positive Lebesgue measure.
-/
def JensenContactSetPositiveMeasureTheorem (n : Nat) : Prop :=
  ∀ f : Point n -> Real,
    (∃ lambda : Real, CoordinateSemiconvexOn lambda Set.univ f) ->
    ∀ x0 : Point n, StrictLocalMax f x0 ->
    ∀ r delta : Real, 0 < r -> 0 < delta ->
      0 < volume (JensenContactSet f x0 r delta)

/--
Jensen's contact-set theorem together with Aleksandrov's theorem supplies a
contact point where a second-order jet exists.
-/
theorem exists_contactPoint_hasSomeSecondOrderJet
    (hJensen : JensenContactSetPositiveMeasureTheorem n)
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsTheorem n)
    {f : Point n -> Real}
    (hsemi : ∃ lambda : Real, CoordinateSemiconvexOn lambda Set.univ f)
    {x0 : Point n} (hstrict : StrictLocalMax f x0)
    {r delta : Real} (hr : 0 < r) (hdelta : 0 < delta) :
    ∃ x : Point n, x ∈ JensenContactSet f x0 r delta ∧ HasSomeSecondOrderJet f x := by
  exact exists_mem_of_measure_pos_of_measure_compl_property_zero
    (K := JensenContactSet f x0 r delta)
    (P := HasSomeSecondOrderJet f)
    (hJensen f hsemi x0 hstrict r delta hr hdelta)
    (hAleksandrov f hsemi)

/--
Jensen's contact-set theorem on a closed ball together with the localized
Aleksandrov theorem supplies a contact point where a second-order jet exists.
-/
theorem exists_contactPoint_hasSomeSecondOrderJet_closedBall
    (hJensen : JensenContactSetPositiveMeasureOnClosedBallTheorem n)
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem n)
    {f : Point n -> Real}
    {x0 : Point n} {r : Real} (hr : 0 < r)
    (hsemi : ∃ lambda : Real, CoordinateSemiconvexOn lambda (Metric.closedBall x0 r) f)
    (hstrict : StrictLocalMax f x0)
    {delta : Real} (hdelta : 0 < delta) :
    ∃ x : Point n, x ∈ JensenContactSet f x0 r delta ∧ HasSomeSecondOrderJet f x := by
  refine exists_mem_of_measure_pos_of_measure_inter_compl_property_zero
    (K := JensenContactSet f x0 r delta)
    (P := HasSomeSecondOrderJet f)
    (hJensen f x0 r hr hsemi hstrict delta hdelta) ?_
  have hnull :=
    hAleksandrov f x0 r hr hsemi
  refine measure_mono_null ?_ hnull
  intro x hx
  exact ⟨hx.1.1, hx.2⟩

/--
Unpacked form of `exists_contactPoint_hasSomeSecondOrderJet`.

In quantified mathematical form, under Jensen's contact-set theorem and
Aleksandrov's theorem, if `f` is semiconvex and has a strict local maximum at
`x0`, then for every `r > 0` and `delta > 0` there exist `x`, `q`, `a`, and
`X` such that

* `x ∈ B(x0, r)`;
* `q ∈ B(0, delta)`;
* `X` is Hermitian;
* `y ↦ f y + q · y` has a local maximum at `x`;
* `(a, X)` is a second-order jet of `f` at `x`.
-/
theorem exists_contactPoint_data_hasSecondOrderJet
    (hJensen : JensenContactSetPositiveMeasureTheorem n)
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsTheorem n)
    {f : Point n -> Real}
    (hsemi : ∃ lambda : Real, CoordinateSemiconvexOn lambda Set.univ f)
    {x0 : Point n} (hstrict : StrictLocalMax f x0)
    {r delta : Real} (hr : 0 < r) (hdelta : 0 < delta) :
    ∃ x : Point n, ∃ q : Point n, ∃ a : Point n, ∃ X : Hessian n,
      x ∈ Metric.closedBall x0 r ∧
        q ∈ Metric.ball 0 delta ∧
        X.IsHermitian ∧
        IsLocalMax (linearPerturbation f q) x ∧
        HasSecondOrderJet f x a X := by
  rcases exists_contactPoint_hasSomeSecondOrderJet
      hJensen hAleksandrov hsemi hstrict hr hdelta with
    ⟨x, hxContact, hxJet⟩
  rcases hxContact with ⟨hxBall, q, hqBall, hqMax⟩
  rcases hxJet with ⟨a, X, hX, hjet⟩
  exact ⟨x, q, a, X, hxBall, hqBall, hX, hqMax, hjet⟩

/--
Unpacked form of `exists_contactPoint_hasSomeSecondOrderJet_closedBall`.

In quantified mathematical form, under the localized Jensen contact-set
theorem and localized Aleksandrov theorem, if `f` is semiconvex on
`closedBall x0 r`, has a strict local maximum at `x0`, `0 < r`, and
`0 < delta`, then there exist `x`, `q`, `a`, and `X` such that

* `x ∈ closedBall x0 r`;
* `q ∈ ball 0 delta`;
* `X` is Hermitian;
* `y ↦ f y + q · y` has a local maximum at `x`;
* `(a, X)` is a second-order jet of `f` at `x`.
-/
theorem exists_contactPoint_data_hasSecondOrderJet_closedBall
    (hJensen : JensenContactSetPositiveMeasureOnClosedBallTheorem n)
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem n)
    {f : Point n -> Real}
    {x0 : Point n} {r : Real} (hr : 0 < r)
    (hsemi : ∃ lambda : Real, CoordinateSemiconvexOn lambda (Metric.closedBall x0 r) f)
    (hstrict : StrictLocalMax f x0)
    {delta : Real} (hdelta : 0 < delta) :
    ∃ x : Point n, ∃ q : Point n, ∃ a : Point n, ∃ X : Hessian n,
      x ∈ Metric.closedBall x0 r ∧
        q ∈ Metric.ball 0 delta ∧
        X.IsHermitian ∧
        IsLocalMax (linearPerturbation f q) x ∧
        HasSecondOrderJet f x a X := by
  rcases exists_contactPoint_hasSomeSecondOrderJet_closedBall
      hJensen hAleksandrov hr hsemi hstrict hdelta with
    ⟨x, hxContact, hxJet⟩
  rcases hxContact with ⟨hxBall, q, hqBall, hqMax⟩
  rcases hxJet with ⟨a, X, hX, hjet⟩
  exact ⟨x, q, a, X, hxBall, hqBall, hX, hqMax, hjet⟩

/--
At a contact point provided by Jensen's contact-set theorem and
Aleksandrov's differentiability theorem, the local-maximum calculus theorem
gives the first- and second-order inequalities.
-/
theorem exists_contactPoint_data_localMaxCalculus
    (hJensen : JensenContactSetPositiveMeasureTheorem n)
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsTheorem n)
    {f : Point n -> Real}
    (hsemi : ∃ lambda : Real, CoordinateSemiconvexOn lambda Set.univ f)
    {x0 : Point n} (hstrict : StrictLocalMax f x0)
    {r delta : Real} (hr : 0 < r) (hdelta : 0 < delta) :
    ∃ x : Point n, ∃ q : Point n, ∃ a : Point n, ∃ X : Hessian n,
      x ∈ Metric.closedBall x0 r ∧
        q ∈ Metric.ball 0 delta ∧
        X.IsHermitian ∧
        IsLocalMax (linearPerturbation f q) x ∧
        HasSecondOrderJet f x a X ∧
        a + q = 0 ∧
        X <= 0 := by
  rcases exists_contactPoint_data_hasSecondOrderJet
      hJensen hAleksandrov hsemi hstrict hr hdelta with
    ⟨x, q, a, X, hxBall, hqBall, hX, hmax, hjet⟩
  have hcalc :=
    localMaxSecondOrderJetCalculusTheorem.apply_linearPerturbation
      (n := n) hX hmax hjet
  exact ⟨x, q, a, X, hxBall, hqBall, hX, hmax, hjet, hcalc⟩

/--
At a contact point supplied by the localized Jensen and Aleksandrov theorems,
the local-maximum calculus theorem gives the first- and second-order
inequalities.
-/
theorem exists_contactPoint_data_localMaxCalculus_closedBall
    (hJensen : JensenContactSetPositiveMeasureOnClosedBallTheorem n)
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem n)
    {f : Point n -> Real}
    {x0 : Point n} {r : Real} (hr : 0 < r)
    (hsemi : ∃ lambda : Real, CoordinateSemiconvexOn lambda (Metric.closedBall x0 r) f)
    (hstrict : StrictLocalMax f x0)
    {delta : Real} (hdelta : 0 < delta) :
    ∃ x : Point n, ∃ q : Point n, ∃ a : Point n, ∃ X : Hessian n,
      x ∈ Metric.closedBall x0 r ∧
        q ∈ Metric.ball 0 delta ∧
        X.IsHermitian ∧
        IsLocalMax (linearPerturbation f q) x ∧
        HasSecondOrderJet f x a X ∧
        a + q = 0 ∧
        X <= 0 := by
  rcases exists_contactPoint_data_hasSecondOrderJet_closedBall
      hJensen hAleksandrov hr hsemi hstrict hdelta with
    ⟨x, q, a, X, hxBall, hqBall, hX, hmax, hjet⟩
  have hcalc :=
    localMaxSecondOrderJetCalculusTheorem.apply_linearPerturbation
      (n := n) hX hmax hjet
  exact ⟨x, q, a, X, hxBall, hqBall, hX, hmax, hjet, hcalc⟩

/--
The contact-point data for the strictified quadratic objective used in the
convex matrix theorem.
-/
theorem exists_strictifiedQuadraticObjective_contactPoint_data_hasSecondOrderJet
    (hJensen : JensenContactSetPositiveMeasureTheorem n)
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsTheorem n)
    {g : Point n -> Real} {B : Hessian n}
    (hsemi :
      ∃ lambda : Real,
        CoordinateSemiconvexOn lambda Set.univ (strictifiedQuadraticObjective g B))
    (hmax : IsMaxOn (semiconvexQuadraticObjective g B) Set.univ 0)
    {r delta : Real} (hr : 0 < r) (hdelta : 0 < delta) :
    ∃ x : Point n, ∃ q : Point n, ∃ a : Point n, ∃ X : Hessian n,
      x ∈ Metric.closedBall (0 : Point n) r ∧
        q ∈ Metric.ball 0 delta ∧
        X.IsHermitian ∧
        IsLocalMax (linearPerturbation (strictifiedQuadraticObjective g B) q) x ∧
        HasSecondOrderJet (strictifiedQuadraticObjective g B) x a X := by
  exact exists_contactPoint_data_hasSecondOrderJet
    hJensen hAleksandrov hsemi
    (strictLocalMax_strictifiedQuadraticObjective_of_isMaxOn_univ hmax)
    hr hdelta

/--
Localized unpacked source-proof data for the strictified quadratic objective.

In quantified mathematical form, assume the localized Jensen contact-set
theorem, the localized Aleksandrov theorem, `g` is convex on `R^n`, and
`x ↦ g x - (1 / 2) * ⟪B x, x⟫` has a maximum at `0` on all of `R^n`. Then
for every `r > 0` and every `delta > 0` there exist `x`, `q`, `a`, and `X`
such that `x ∈ closedBall 0 r`, `q ∈ ball 0 delta`, `X` is Hermitian,
`y ↦ strictifiedQuadraticObjective g B y + q · y` has a local maximum at
`x`, and `(a, X)` is a second-order jet of `strictifiedQuadraticObjective g B`
at `x`.
-/
theorem exists_strictifiedQuadraticObjective_contactPoint_data_hasSecondOrderJet_closedBall
    (hJensen : JensenContactSetPositiveMeasureOnClosedBallTheorem n)
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem n)
    {g : Point n -> Real} {B : Hessian n}
    (hconv : ConvexOn Real Set.univ g)
    (hmax : IsMaxOn (semiconvexQuadraticObjective g B) Set.univ 0)
    {r delta : Real} (hr : 0 < r) (hdelta : 0 < delta) :
    ∃ x : Point n, ∃ q : Point n, ∃ a : Point n, ∃ X : Hessian n,
      x ∈ Metric.closedBall (0 : Point n) r ∧
        q ∈ Metric.ball 0 delta ∧
        X.IsHermitian ∧
        IsLocalMax (linearPerturbation (strictifiedQuadraticObjective g B) q) x ∧
        HasSecondOrderJet (strictifiedQuadraticObjective g B) x a X := by
  have hsemi :=
    exists_coordinateSemiconvexOn_strictifiedQuadraticObjective_closedBall
      (n := n) (B := B) hconv (le_of_lt hr)
  exact exists_contactPoint_data_hasSecondOrderJet_closedBall
    hJensen hAleksandrov hr hsemi
    (strictLocalMax_strictifiedQuadraticObjective_of_isMaxOn_univ hmax)
    hdelta

/--
At a contact point for the strictified quadratic objective, the
local-maximum calculus theorem gives the first- and second-order inequalities.
-/
theorem exists_strictifiedQuadraticObjective_contactPoint_data_localMaxCalculus
    (hJensen : JensenContactSetPositiveMeasureTheorem n)
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsTheorem n)
    {g : Point n -> Real} {B : Hessian n}
    (hsemi :
      ∃ lambda : Real,
        CoordinateSemiconvexOn lambda Set.univ (strictifiedQuadraticObjective g B))
    (hmax : IsMaxOn (semiconvexQuadraticObjective g B) Set.univ 0)
    {r delta : Real} (hr : 0 < r) (hdelta : 0 < delta) :
    ∃ x : Point n, ∃ q : Point n, ∃ a : Point n, ∃ X : Hessian n,
      x ∈ Metric.closedBall (0 : Point n) r ∧
        q ∈ Metric.ball 0 delta ∧
        X.IsHermitian ∧
        IsLocalMax (linearPerturbation (strictifiedQuadraticObjective g B) q) x ∧
        HasSecondOrderJet (strictifiedQuadraticObjective g B) x a X ∧
        a + q = 0 ∧
        X <= 0 := by
  exact exists_contactPoint_data_localMaxCalculus
    hJensen hAleksandrov hsemi
    (strictLocalMax_strictifiedQuadraticObjective_of_isMaxOn_univ hmax)
    hr hdelta

/--
Localized source-proof data for the strictified quadratic objective, together
with the local-maximum calculus conclusions.
-/
theorem exists_strictifiedQuadraticObjective_contactPoint_data_localMaxCalculus_closedBall
    (hJensen : JensenContactSetPositiveMeasureOnClosedBallTheorem n)
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem n)
    {g : Point n -> Real} {B : Hessian n}
    (hconv : ConvexOn Real Set.univ g)
    (hmax : IsMaxOn (semiconvexQuadraticObjective g B) Set.univ 0)
    {r delta : Real} (hr : 0 < r) (hdelta : 0 < delta) :
    ∃ x : Point n, ∃ q : Point n, ∃ a : Point n, ∃ X : Hessian n,
      x ∈ Metric.closedBall (0 : Point n) r ∧
        q ∈ Metric.ball 0 delta ∧
        X.IsHermitian ∧
        IsLocalMax (linearPerturbation (strictifiedQuadraticObjective g B) q) x ∧
        HasSecondOrderJet (strictifiedQuadraticObjective g B) x a X ∧
        a + q = 0 ∧
        X <= 0 := by
  have hsemi :=
    exists_coordinateSemiconvexOn_strictifiedQuadraticObjective_closedBall
      (n := n) (B := B) hconv (le_of_lt hr)
  exact exists_contactPoint_data_localMaxCalculus_closedBall
    hJensen hAleksandrov hr hsemi
    (strictLocalMax_strictifiedQuadraticObjective_of_isMaxOn_univ hmax)
    hdelta

/--
Source-proof data for the strictified quadratic objective, expressed as closed
superjet data for the original function.

In quantified mathematical form, assume Jensen's contact-set theorem,
Aleksandrov's differentiability theorem, semiconvexity of
`x ↦ g x - (1 / 2) * ⟪B x, x⟫ - (∑ i, x_i^2)^2`, and that
`x ↦ g x - (1 / 2) * ⟪B x, x⟫` has a maximum at `0`. Then for every
`r > 0` and every `delta > 0` there exist `x`, `q`, `a`, and `X` such that
`x ∈ closedBall 0 r`, `q ∈ ball 0 delta`, `X` is Hermitian,
`a + q = 0`, `X ≤ 0`, and after adding the coordinate-quartic jet at `x`
and the recentered quadratic jet at `x`, the resulting jet belongs to
`\overline J^{2,+}_{R^n} g(x)`. Its Hessian component is at most
`B + (coordinate-quartic Hessian at x)` in the Loewner order.
-/
theorem exists_strictifiedQuadraticObjective_closedSuperjet_data
    (hJensen : JensenContactSetPositiveMeasureTheorem n)
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsTheorem n)
    {g : Point n -> Real} {B : Hessian n}
    (hsemi :
      ∃ lambda : Real,
        CoordinateSemiconvexOn lambda Set.univ (strictifiedQuadraticObjective g B))
    (hmax : IsMaxOn (semiconvexQuadraticObjective g B) Set.univ 0)
    {r delta : Real} (hr : 0 < r) (hdelta : 0 < delta) :
    ∃ x : Point n, ∃ q : Point n, ∃ a : Point n, ∃ X : Hessian n,
      x ∈ Metric.closedBall (0 : Point n) r ∧
        q ∈ Metric.ball 0 delta ∧
        X.IsHermitian ∧
        HasSecondOrderJet (strictifiedQuadraticObjective g B) x a X ∧
        a + q = 0 ∧
        X <= 0 ∧
        (({ gradient := a, hessian := X } : Jet n) + coordinateQuarticJetAt x) +
            quadraticModelJetAt 0 0 B x ∈ ClosedSuperjet Set.univ g x ∧
        (((( { gradient := a, hessian := X } : Jet n) + coordinateQuarticJetAt x) +
            quadraticModelJetAt 0 0 B x).hessian) <=
          (coordinateQuarticJetAt x).hessian + B := by
  rcases exists_strictifiedQuadraticObjective_contactPoint_data_localMaxCalculus
      hJensen hAleksandrov hsemi hmax hr hdelta with
    ⟨x, q, a, X, hxBall, hqBall, hX, _hmaxPerturbed, hjet, ha, hXle⟩
  exact ⟨x, q, a, X, hxBall, hqBall, hX, hjet, ha, hXle,
    hjet.closedSuperjet_of_strictifiedQuadraticObjective,
    strictifiedQuadraticObjective_closedSuperjetJet_hessian_le hXle⟩

/--
Localized source-proof data for the strictified quadratic objective, expressed
as closed superjet data for the original function.

In quantified mathematical form, assume the localized Jensen contact-set
theorem, the localized Aleksandrov theorem, `g` is convex on `R^n`, and
`x ↦ g x - (1 / 2) * ⟪B x, x⟫` has a maximum at `0`. Then for every
`r > 0` and every `delta > 0` there exist `x`, `q`, `a`, and `X` such that
`x ∈ closedBall 0 r`, `q ∈ ball 0 delta`, `X` is Hermitian, `a + q = 0`,
`X ≤ 0`, and after adding the coordinate-quartic jet at `x` and the
recentered quadratic jet at `x`, the resulting jet belongs to
`\overline J^{2,+}_{R^n} g(x)`. Its Hessian component is at most
`B + (coordinate-quartic Hessian at x)` in the Loewner order.
-/
theorem exists_strictifiedQuadraticObjective_closedSuperjet_data_closedBall
    (hJensen : JensenContactSetPositiveMeasureOnClosedBallTheorem n)
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem n)
    {g : Point n -> Real} {B : Hessian n}
    (hconv : ConvexOn Real Set.univ g)
    (hmax : IsMaxOn (semiconvexQuadraticObjective g B) Set.univ 0)
    {r delta : Real} (hr : 0 < r) (hdelta : 0 < delta) :
    ∃ x : Point n, ∃ q : Point n, ∃ a : Point n, ∃ X : Hessian n,
      x ∈ Metric.closedBall (0 : Point n) r ∧
        q ∈ Metric.ball 0 delta ∧
        X.IsHermitian ∧
        HasSecondOrderJet (strictifiedQuadraticObjective g B) x a X ∧
        a + q = 0 ∧
        X <= 0 ∧
        (({ gradient := a, hessian := X } : Jet n) + coordinateQuarticJetAt x) +
            quadraticModelJetAt 0 0 B x ∈ ClosedSuperjet Set.univ g x ∧
        (((( { gradient := a, hessian := X } : Jet n) + coordinateQuarticJetAt x) +
            quadraticModelJetAt 0 0 B x).hessian) <=
          (coordinateQuarticJetAt x).hessian + B := by
  rcases exists_strictifiedQuadraticObjective_contactPoint_data_localMaxCalculus_closedBall
      hJensen hAleksandrov hconv hmax hr hdelta with
    ⟨x, q, a, X, hxBall, hqBall, hX, _hmaxPerturbed, hjet, ha, hXle⟩
  exact ⟨x, q, a, X, hxBall, hqBall, hX, hjet, ha, hXle,
    hjet.closedSuperjet_of_strictifiedQuadraticObjective,
    strictifiedQuadraticObjective_closedSuperjetJet_hessian_le hXle⟩

/--
Localized selected closed-superjet data with explicit estimates on the base
point and first-order component.

In quantified mathematical form, under the same hypotheses as
`exists_strictifiedQuadraticObjective_closedSuperjet_data_closedBall`, for
every `r > 0` and every `delta > 0` there exist `x`, `a`, and a jet `J` such
that

* `‖x‖ ≤ r`;
* `‖a‖ < delta`;
* `J ∈ \overline J^{2,+}_{R^n} g(x)`;
* `J.hessian ≤ B + (coordinate-quartic Hessian at x)`;
* `J` is obtained from a two-sided jet of the strictified quadratic objective
  by adding back the coordinate-quartic and quadratic jets.
-/
theorem exists_strictifiedQuadraticObjective_closedSuperjet_data_closedBall_norm_bounds
    (hJensen : JensenContactSetPositiveMeasureOnClosedBallTheorem n)
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem n)
    {g : Point n -> Real} {B : Hessian n}
    (hconv : ConvexOn Real Set.univ g)
    (hmax : IsMaxOn (semiconvexQuadraticObjective g B) Set.univ 0)
    {r delta : Real} (hr : 0 < r) (hdelta : 0 < delta) :
    ∃ x : Point n, ∃ a : Point n, ∃ X : Hessian n, ∃ J : Jet n,
      ‖x‖ <= r ∧
        ‖a‖ < delta ∧
        X.IsHermitian ∧
        HasSecondOrderJet (strictifiedQuadraticObjective g B) x a X ∧
        J =
          (({ gradient := a, hessian := X } : Jet n) + coordinateQuarticJetAt x) +
            quadraticModelJetAt 0 0 B x ∧
        J ∈ ClosedSuperjet Set.univ g x ∧
        J.hessian <= (coordinateQuarticJetAt x).hessian + B := by
  rcases exists_strictifiedQuadraticObjective_closedSuperjet_data_closedBall
      hJensen hAleksandrov hconv hmax hr hdelta with
    ⟨x, q, a, X, hxBall, hqBall, hX, hjet, ha, _hXle, hclosed, hupper⟩
  have hxnorm : ‖x‖ <= r := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hxBall
  have ha_eq : a = -q := by
    rw [← sub_eq_zero] at ha ⊢
    simpa [sub_eq_add_neg, add_comm] using ha
  have hqnorm : ‖q‖ < delta := by
    simpa [Metric.mem_ball, dist_eq_norm] using hqBall
  have hanorm : ‖a‖ < delta := by
    simpa [ha_eq] using hqnorm
  let J : Jet n :=
    (({ gradient := a, hessian := X } : Jet n) + coordinateQuarticJetAt x) +
      quadraticModelJetAt 0 0 B x
  exact ⟨x, a, X, J, hxnorm, hanorm, hX, hjet, rfl, hclosed, hupper⟩

/--
Localized selected closed-superjet data with norm bounds and Hermitian
selected Hessian.

In quantified mathematical form, this is the preceding selected-data theorem
with the additional conclusion that the Hessian component of the produced
closed-superjet jet is Hermitian, assuming the quadratic matrix `B` is
Hermitian.
-/
theorem exists_strictifiedQuadraticObjective_closedSuperjet_data_closedBall_norm_bounds_hessian
    (hJensen : JensenContactSetPositiveMeasureOnClosedBallTheorem n)
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem n)
    {g : Point n -> Real} {B : Hessian n}
    (hB : B.IsHermitian)
    (hconv : ConvexOn Real Set.univ g)
    (hmax : IsMaxOn (semiconvexQuadraticObjective g B) Set.univ 0)
    {r delta : Real} (hr : 0 < r) (hdelta : 0 < delta) :
    ∃ x : Point n, ∃ a : Point n, ∃ X : Hessian n, ∃ J : Jet n,
      ‖x‖ <= r ∧
        ‖a‖ < delta ∧
        X.IsHermitian ∧
        J.hessian.IsHermitian ∧
        HasSecondOrderJet (strictifiedQuadraticObjective g B) x a X ∧
        J =
          (({ gradient := a, hessian := X } : Jet n) + coordinateQuarticJetAt x) +
            quadraticModelJetAt 0 0 B x ∧
        J ∈ ClosedSuperjet Set.univ g x ∧
        J.hessian <= (coordinateQuarticJetAt x).hessian + B := by
  rcases exists_strictifiedQuadraticObjective_closedSuperjet_data_closedBall_norm_bounds
      hJensen hAleksandrov hconv hmax hr hdelta with
    ⟨x, a, X, J, hxnorm, hanorm, hX, hjet, hJ, hclosed, hupper⟩
  have hJherm : J.hessian.IsHermitian := by
    rw [hJ]
    exact strictifiedQuadraticObjective_closedSuperjetJet_hessian_isHermitian hX hB
  exact ⟨x, a, X, J, hxnorm, hanorm, hX, hJherm, hjet, hJ, hclosed, hupper⟩

/--
Selected closed-superjet data along the sequence `1 / (k + 1)`.

In standard mathematical terms, under the hypotheses of the localized
Aleksandrov--Jensen selected-data theorem, one can choose, for every natural
number `k`, a point `x_k`, a vector `a_k`, a Hessian `X_k`, and a closed
superjet `J_k ∈ \overline J^{2,+}_{R^n} g(x_k)` such that

`‖x_k‖ ≤ 1 / (k + 1)`, `‖a_k‖ < 1 / (k + 1)`,

and therefore `x_k -> 0` and `a_k -> 0`. The theorem also records the exact
formula for `J_k` and the Hessian upper bound used in the limiting argument.
-/
theorem exists_strictifiedQuadraticObjective_closedSuperjet_sequence_norm_bounds_hessian
    (hJensen : JensenContactSetPositiveMeasureOnClosedBallTheorem n)
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem n)
    {g : Point n -> Real} {B : Hessian n}
    (hB : B.IsHermitian)
    (hconv : ConvexOn Real Set.univ g)
    (hmax : IsMaxOn (semiconvexQuadraticObjective g B) Set.univ 0) :
    ∃ xSeq : Nat -> Point n, ∃ aSeq : Nat -> Point n,
    ∃ XSeq : Nat -> Hessian n, ∃ JSeq : Nat -> Jet n,
      (∀ k : Nat, ‖xSeq k‖ <= (1 : Real) / ((k : Real) + 1)) ∧
      (∀ k : Nat, ‖aSeq k‖ < (1 : Real) / ((k : Real) + 1)) ∧
      Filter.Tendsto xSeq Filter.atTop (𝓝 (0 : Point n)) ∧
      Filter.Tendsto aSeq Filter.atTop (𝓝 (0 : Point n)) ∧
      (∀ k : Nat, (XSeq k).IsHermitian) ∧
      (∀ k : Nat, (JSeq k).hessian.IsHermitian) ∧
      (∀ k : Nat,
        HasSecondOrderJet (strictifiedQuadraticObjective g B)
          (xSeq k) (aSeq k) (XSeq k)) ∧
      (∀ k : Nat,
        JSeq k =
          (({ gradient := aSeq k, hessian := XSeq k } : Jet n) +
              coordinateQuarticJetAt (xSeq k)) +
            quadraticModelJetAt 0 0 B (xSeq k)) ∧
      (∀ k : Nat, JSeq k ∈ ClosedSuperjet Set.univ g (xSeq k)) ∧
      (∀ k : Nat,
        (JSeq k).hessian <= (coordinateQuarticJetAt (xSeq k)).hessian + B) := by
  classical
  let eps : Nat -> Real := fun k => (1 : Real) / ((k : Real) + 1)
  have heps_pos : ∀ k : Nat, 0 < eps k := by
    intro k
    dsimp [eps]
    positivity
  have hselect :
      ∀ k : Nat,
        ∃ x : Point n, ∃ a : Point n, ∃ X : Hessian n, ∃ J : Jet n,
          ‖x‖ <= eps k ∧
            ‖a‖ < eps k ∧
            X.IsHermitian ∧
            J.hessian.IsHermitian ∧
            HasSecondOrderJet (strictifiedQuadraticObjective g B) x a X ∧
            J =
              (({ gradient := a, hessian := X } : Jet n) +
                  coordinateQuarticJetAt x) +
                quadraticModelJetAt 0 0 B x ∧
            J ∈ ClosedSuperjet Set.univ g x ∧
            J.hessian <= (coordinateQuarticJetAt x).hessian + B := by
    intro k
    simpa [eps] using
      exists_strictifiedQuadraticObjective_closedSuperjet_data_closedBall_norm_bounds_hessian
        hJensen hAleksandrov hB hconv hmax
        (hr := heps_pos k) (hdelta := heps_pos k)
  choose xSeq aSeq XSeq JSeq hdata using hselect
  have hx_bound : ∀ k : Nat, ‖xSeq k‖ <= eps k := by
    intro k
    exact (hdata k).1
  have ha_bound : ∀ k : Nat, ‖aSeq k‖ < eps k := by
    intro k
    exact (hdata k).2.1
  have heps_tendsto : Filter.Tendsto eps Filter.atTop (𝓝 0) := by
    simpa [eps] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))
  have hx_norm_tendsto :
      Filter.Tendsto (fun k : Nat => ‖xSeq k‖) Filter.atTop (𝓝 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun k => norm_nonneg (xSeq k)) ?_
      heps_tendsto
    exact Filter.Eventually.of_forall hx_bound
  have ha_norm_tendsto :
      Filter.Tendsto (fun k : Nat => ‖aSeq k‖) Filter.atTop (𝓝 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun k => norm_nonneg (aSeq k)) ?_
      heps_tendsto
    exact Filter.Eventually.of_forall fun k => le_of_lt (ha_bound k)
  have hx_tendsto : Filter.Tendsto xSeq Filter.atTop (𝓝 (0 : Point n)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa using hx_norm_tendsto
  have ha_tendsto : Filter.Tendsto aSeq Filter.atTop (𝓝 (0 : Point n)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa using ha_norm_tendsto
  refine ⟨xSeq, aSeq, XSeq, JSeq, ?_, ?_, hx_tendsto, ha_tendsto, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [eps] using hx_bound
  · simpa [eps] using ha_bound
  · intro k
    exact (hdata k).2.2.1
  · intro k
    exact (hdata k).2.2.2.1
  · intro k
    exact (hdata k).2.2.2.2.1
  · intro k
    exact (hdata k).2.2.2.2.2.1
  · intro k
    exact (hdata k).2.2.2.2.2.2.1
  · intro k
    exact (hdata k).2.2.2.2.2.2.2

end ViscositySolns
