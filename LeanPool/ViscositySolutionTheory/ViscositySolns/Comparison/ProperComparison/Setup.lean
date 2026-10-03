/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Comparison.CILMaximumPrinciple
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Comparison.OperatorCondition
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Comparison.ProperComparison.Localization
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Solutions

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Strictification and theorem-shaped hypotheses for proper comparison.
-/

@[expose] public noncomputable section

open Filter
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
The theorem-shaped proposition for the proper comparison result with the
operator hypotheses already formalized in this repository.

The predicate `extraHypotheses u v` is reserved for the boundary, boundedness,
and localization assumptions required by the global comparison proof. With
those assumptions, every upper semicontinuous viscosity subsolution `u` and
every lower semicontinuous viscosity supersolution `v` should satisfy
`u ≤ v` on `C`.
-/
def ProperComparisonStatementOn
    (C : Set (Point n)) (R : Set Real) (F : Operator n)
    (extraHypotheses : (Point n -> Real) -> (Point n -> Real) -> Prop) : Prop :=
  Proper F ->
  OperatorContinuous F ->
  IshiiOperatorComparisonConditionOn C R F ->
  ∀ u v : Point n -> Real,
    extraHypotheses u v ->
    ViscositySubsolution C F u ->
    ViscositySupersolution C F v ->
    (∀ x : Point n, x ∈ C -> u x ∈ R) ->
      ComparisonConclusionOn C u v

/--
The theorem-shaped proposition for the first boundary-value comparison target.

It says that, under properness, operator continuity, the Ishii structural
condition, boundary comparison on `frontier C`, the scalar-range condition
`u x ∈ R` for `x ∈ C`, and compactness of `closure C`, every viscosity
subsolution `u` is bounded above by every viscosity supersolution `v` on `C`.
-/
def ProperBoundaryComparisonStatementOn
    (C : Set (Point n)) (R : Set Real) (F : Operator n) : Prop :=
  ProperComparisonStatementOn C R F (BoundaryComparisonHypothesesOn C R)

theorem ProperBoundaryComparisonStatementOn.unfold
    {C : Set (Point n)} {R : Set Real} {F : Operator n}
    (h : ProperBoundaryComparisonStatementOn C R F) :
    Proper F ->
    OperatorContinuous F ->
    IshiiOperatorComparisonConditionOn C R F ->
    ∀ u v : Point n -> Real,
      BoundaryComparisonOn C u v ->
      ScalarRangeOn C R u ->
      CompactClosure C ->
      ViscositySubsolution C F u ->
      ViscositySupersolution C F v ->
        ComparisonConclusionOn C u v := by
  intro hproper hcont hcomp u v hbd hry hcompact hu hv
  exact h hproper hcont hcomp u v ⟨hbd, hry, hcompact⟩ hu hv hry

/--
Unbounded-scalar version of `ProperBoundaryComparisonStatementOn`.

In quantified mathematical form, if the scalar set is all real numbers, then
the scalar-range condition is automatic: for every `x ∈ C`,
`u x ∈ Set.univ`.
-/
theorem ProperBoundaryComparisonStatementOn.unfold_univScalar
    {C : Set (Point n)} {F : Operator n}
    (h : ProperBoundaryComparisonStatementOn C Set.univ F) :
    Proper F ->
    OperatorContinuous F ->
    IshiiOperatorComparisonConditionOn C Set.univ F ->
    ∀ u v : Point n -> Real,
      BoundaryComparisonOn C u v ->
      CompactClosure C ->
      ViscositySubsolution C F u ->
      ViscositySupersolution C F v ->
        ComparisonConclusionOn C u v := by
  intro hproper hcont hcomp u v hbd hcompact hu hv
  exact h.unfold hproper hcont hcomp u v hbd (ScalarRangeOn.univ C u) hcompact hu hv

/--
Let `ω` be a comparison modulus and let `ε > 0`. Let `t i` be a family of
real numbers which converges to `0` through positive values along a nontrivial
filter `l`. Then it is impossible that `ε ≤ ω (t i)` holds for all `i` in a
set belonging to `l`.
-/
theorem not_eventually_strict_le_modulus_of_tendsto_nhdsWithin_Ioi
    {ι : Type*} {l : Filter ι} [NeBot l] {ω : Real -> Real} {ε : Real}
    {t : ι -> Real}
    (hω : ComparisonModulus ω) (hε : 0 < ε)
    (ht : Tendsto t l (nhdsWithin 0 (Set.Ioi 0))) :
    ¬ ∀ᶠ i in l, ε <= ω (t i) := by
  intro hle
  have hlt : ∀ᶠ i in l, ω (t i) < ε :=
    (hω.tendsto_zero.comp ht) (Iio_mem_nhds hε)
  have hfalse : ∀ᶠ i in l, False := by
    filter_upwards [hle, hlt] with i hlei hlti
    exact (not_le_of_gt hlti) hlei
  exact NeBot.ne inferInstance (eventually_false_iff_eq_bot.mp hfalse)

/--
Strict viscosity subsolution with margin `ε`: for every superjet, the
viscosity inequality is `F x (u x) p X ≤ -ε`.
-/
def StrictViscositySubsolution
    (C : Set (Point n)) (F : Operator n) (ε : Real) (u : Point n -> Real) : Prop :=
  UpperSemicontinuousOn u C ∧
    ∀ x : Point n, x ∈ C -> ∀ J : Jet n, J ∈ Superjet C u x ->
      F x (u x) J.gradient J.hessian <= -ε

theorem StrictViscositySubsolution.upperSemicontinuousOn
    {C : Set (Point n)} {F : Operator n} {ε : Real} {u : Point n -> Real}
    (hu : StrictViscositySubsolution C F ε u) :
    UpperSemicontinuousOn u C :=
  hu.1

theorem StrictViscositySubsolution.closedSuperjet_le_neg_of_operatorContinuous
    {C : Set (Point n)} {F : Operator n} {ε : Real} {u : Point n -> Real}
    {x : Point n} {J : Jet n}
    (hu : StrictViscositySubsolution C F ε u)
    (hF : OperatorContinuous F)
    (hJ : J ∈ ClosedSuperjet C u x) :
    F x (u x) J.gradient J.hessian <= -ε :=
  closedSuperjet_induction
    (isClosed_Iic.preimage hF.continuous)
    (fun y hy K hK => hu.2 y hy K hK) hJ

theorem StrictViscositySubsolution.to_viscositySubsolution
    {C : Set (Point n)} {F : Operator n} {ε : Real} {u : Point n -> Real}
    (hu : StrictViscositySubsolution C F ε u) (hε : 0 <= ε) :
    ViscositySubsolution C F u := by
  refine ⟨hu.upperSemicontinuousOn, ?_⟩
  intro x hx J hJ
  have hstrict := hu.2 x hx J hJ
  linarith

/--
Uniform decrease of the operator under a fixed downward shift in the scalar
unknown.

In quantified mathematical form, `UniformScalarDecreaseOn C F δ ε` means:
for every `x ∈ C`, every scalar `r`, every first-derivative vector `p`, and
every Hessian matrix `X`,

`F x (r - δ) p X ≤ F x r p X - ε`.
-/
def UniformScalarDecreaseOn
    (C : Set (Point n)) (F : Operator n) (δ ε : Real) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ r : Real, ∀ p : Point n, ∀ X : Hessian n,
    F x (r - δ) p X <= F x r p X - ε

/--
A positive lower bound for the zeroth-order coefficient on `C`.

In quantified mathematical form, `ZerothCoefficientLowerBoundOn C c γ` means:
for every `x ∈ C`, one has `γ ≤ c x`.
-/
def ZerothCoefficientLowerBoundOn
    (C : Set (Point n)) (c : Point n -> Real) (γ : Real) : Prop :=
  ∀ x : Point n, x ∈ C -> γ <= c x

/--
Trace-form operators satisfy the uniform scalar-decrease condition when the
zeroth-order coefficient gives the required decrease.

In quantified mathematical form, if `ε ≤ c x * δ` for every `x ∈ C`, then

`F x (r - δ) p X ≤ F x r p X - ε`

for `F = traceSecondOrderOperator A b c f`.
-/
theorem uniformScalarDecreaseOn_traceSecondOrderOperator
    {C : Set (Point n)}
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    {δ ε : Real}
    (hcδ : ∀ x : Point n, x ∈ C -> ε <= c x * δ) :
    UniformScalarDecreaseOn C (traceSecondOrderOperator A b c f) δ ε := by
  intro x hx r p X
  have hxδε : ε <= c x * δ := hcδ x hx
  simp [traceSecondOrderOperator_apply]
  linarith

/--
Trace-form operators satisfy the uniform scalar-decrease condition with
margin `γ * δ` when `0 ≤ δ` and `γ ≤ c x` for every `x ∈ C`.

In quantified mathematical form, if `0 ≤ δ` and `γ ≤ c x` for every `x ∈ C`,
then for every `x ∈ C`, scalar `r`, vector `p`, and matrix `X`,

`F x (r - δ) p X ≤ F x r p X - γ * δ`

for `F = traceSecondOrderOperator A b c f`.
-/
theorem uniformScalarDecreaseOn_traceSecondOrderOperator_of_zeroth_lower_bound
    {C : Set (Point n)}
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    {δ γ : Real}
    (hδ : 0 <= δ) (hcγ : ZerothCoefficientLowerBoundOn C c γ) :
    UniformScalarDecreaseOn C (traceSecondOrderOperator A b c f) δ (γ * δ) := by
  refine uniformScalarDecreaseOn_traceSecondOrderOperator ?_
  intro x hx
  exact mul_le_mul_of_nonneg_right (hcγ x hx) hδ

/--
A non-strict viscosity subsolution becomes a strict viscosity subsolution
after a constant downward shift, provided the operator decreases uniformly
under that scalar shift.

In quantified mathematical form, if `u` is a viscosity subsolution on `C` and
`F x (r - δ) p X ≤ F x r p X - ε` for every `x ∈ C`, `r`, `p`, and `X`, then
`x ↦ u x - δ` is a strict viscosity subsolution with margin `ε` on `C`.
-/
theorem ViscositySubsolution.strict_sub_const_of_uniformScalarDecrease
    {C : Set (Point n)} {F : Operator n} {u : Point n -> Real} {δ ε : Real}
    (hu : ViscositySubsolution C F u)
    (hdec : UniformScalarDecreaseOn C F δ ε) :
    StrictViscositySubsolution C F ε (fun y => u y - δ) := by
  refine ⟨?_, ?_⟩
  · simpa [sub_eq_add_neg] using hu.1.add upperSemicontinuousOn_const
  · intro x hx J hJ
    have hJu : J ∈ Superjet C u x := (superjet_sub_const_iff).1 hJ
    have huJ : F x (u x) J.gradient J.hessian <= 0 := hu.2 x hx J hJu
    have hshift :
        F x (u x - δ) J.gradient J.hessian <=
          F x (u x) J.gradient J.hessian - ε :=
      hdec x hx (u x) J.gradient J.hessian
    calc
      F x ((fun y => u y - δ) x) J.gradient J.hessian =
          F x (u x - δ) J.gradient J.hessian := rfl
      _ <= F x (u x) J.gradient J.hessian - ε := hshift
      _ <= -ε := by linarith

/--
Strictification data on the compact closure of `C`.

In quantified mathematical form, this predicate says that, for every real
number `η > 0`, there exist a real number `ε > 0` and a function `w` such
that:

* the quadratic-penalty conclusion of Ishii's lemma is available for `w` and
  `v` on `closure C`;
* `w` is a strict viscosity subsolution with margin `ε` on `closure C`;
* `w x ∈ R` for every `x ∈ closure C`;
* `u x ≤ w x + η` for every `x ∈ C`.

This is the limiting bridge from non-strict comparison for `u` to strict
comparison for nearby functions `w`.
-/
def CompactClosureStrictificationOn
    (C : Set (Point n)) (R : Set Real) (F : Operator n)
    (u v : Point n -> Real) : Prop :=
  ∀ η : Real, 0 < η ->
    ∃ ε : Real, ∃ w : Point n -> Real,
      0 < ε ∧
      QuadraticPenaltyIshiiLemmaOn (closure C) (closure C) w v ∧
      StrictViscositySubsolution (closure C) F ε w ∧
      ScalarRangeOn (closure C) R w ∧
      ∀ x : Point n, x ∈ C -> u x <= w x + η

/--
Localized strictification using natural-number indexed doubled-variable data.

In quantified mathematical form, this predicate says that, for every real
number `η > 0`, there exist a real number `ε > 0`, a function `w`, functions
`α : ℕ -> ℝ` and `x y : ℕ -> ℝ^n`, such that:

* the quadratic-penalty Ishii lemma holds for `w` and `v` on `C × C`;
* `w` is a strict viscosity subsolution with margin `ε` on `C`;
* `w x ∈ R` for every `x ∈ C`;
* if there exists `z ∈ C` with `v z < w z`, then the selected
  doubled-variable data `α`, `x`, and `y` satisfy the filter-form
  localization statement `StrictDoubledVariableLocalizationAlongOn` along
  `atTop`;
* `u x ≤ w x + η` for every `x ∈ C`.

This formulation is the one used by compact selection and subsequence
arguments: the parameters and selected points are indexed by natural numbers,
and the relevant convergence is expressed along `atTop`.
-/
def LocalizedStrictificationAlongOn
    (C : Set (Point n)) (R : Set Real) (F : Operator n)
    (u v : Point n -> Real) : Prop :=
  ∀ η : Real, 0 < η ->
    ∃ ε : Real, ∃ w : Point n -> Real,
    ∃ α : ℕ -> Real, ∃ x : ℕ -> Point n, ∃ y : ℕ -> Point n,
      0 < ε ∧
      QuadraticPenaltyIshiiLemmaOn C C w v ∧
      StrictViscositySubsolution C F ε w ∧
      ScalarRangeOn C R w ∧
      StrictDoubledVariableLocalizationAlongOn C R w v atTop α x y ∧
      ∀ z : Point n, z ∈ C -> u z <= w z + η

/--
Constant-shift data sufficient for natural-number indexed localized
strictification.

In quantified mathematical form, this predicate says that, for every real
number `η > 0`, there exist real numbers `δ` and `ε`, functions
`α : ℕ -> ℝ` and `x y : ℕ -> ℝ^n`, such that:

* `0 < δ` and `δ ≤ η`;
* `0 < ε`;
* `F x (r - δ) p X ≤ F x r p X - ε` for every `x ∈ C`, scalar `r`,
  first-derivative vector `p`, and Hessian matrix `X`;
* the quadratic-penalty Ishii lemma holds for `x ↦ u x - δ` and `v` on
  `C × C`;
* `u x - δ ∈ R` for every `x ∈ C`;
* the selected data `α`, `x`, and `y` satisfy
  `StrictDoubledVariableLocalizationAlongOn C R (fun x => u x - δ) v atTop α x y`.
-/
def ConstantShiftLocalizedStrictificationAlongDataOn
    (C : Set (Point n)) (R : Set Real) (F : Operator n)
    (u v : Point n -> Real) : Prop :=
  ∀ η : Real, 0 < η ->
    ∃ δ : Real, ∃ ε : Real,
    ∃ α : ℕ -> Real, ∃ x : ℕ -> Point n, ∃ y : ℕ -> Point n,
      0 < δ ∧ δ <= η ∧ 0 < ε ∧
      UniformScalarDecreaseOn C F δ ε ∧
      QuadraticPenaltyIshiiLemmaOn C C (fun x => u x - δ) v ∧
      ScalarRangeOn C R (fun x => u x - δ) ∧
      StrictDoubledVariableLocalizationAlongOn C R (fun x => u x - δ) v atTop α x y

/--
Constant-shift data stated directly in terms of maximizers selected on
`closure C × closure C`.

In quantified mathematical form, this predicate says that, for every real
number `η > 0`, there exist real numbers `δ` and `ε`, functions
`α : ℕ -> ℝ` and `x y : ℕ -> ℝ^n`, and a point `x0 : ℝ^n`, such that:

* `0 < δ` and `δ ≤ η`;
* `0 < ε`;
* `F x (r - δ) p X ≤ F x r p X - ε` for every `x ∈ C`, scalar `r`,
  first-derivative vector `p`, and Hessian matrix `X`;
* the quadratic-penalty Ishii lemma holds for `x ↦ u x - δ` and `v` on
  `C × C`;
* `u x - δ ∈ R` for every `x ∈ C`;
* `x0 ∈ closure C` and `v x0 < u x0 - δ`;
* `x ↦ u x - δ` is upper semicontinuous on `closure C`;
* `v` is lower semicontinuous on `closure C`;
* `x i -> x0` and `y i -> x0` within `closure C` as `i -> ∞`;
* for all `i` in a set belonging to `atTop`, `0 < α i`,
  `x i ∈ closure C`, `y i ∈ closure C`, and `(x i, y i)` maximizes
  `(x', y') ↦ u x' - δ - v y' - (α i / 2) * ∑ j, (x' j - y' j)^2`
  on `closure C × closure C`;
* `α i -> +∞` as `i -> ∞`.
-/
def ConstantShiftClosureMaximizerDataOn
    (C : Set (Point n)) (R : Set Real) (F : Operator n)
    (u v : Point n -> Real) : Prop :=
  ∀ η : Real, 0 < η ->
    ∃ δ : Real, ∃ ε : Real,
    ∃ α : ℕ -> Real, ∃ x : ℕ -> Point n, ∃ y : ℕ -> Point n,
    ∃ x0 : Point n,
      0 < δ ∧ δ <= η ∧ 0 < ε ∧
      UniformScalarDecreaseOn C F δ ε ∧
      QuadraticPenaltyIshiiLemmaOn C C (fun x => u x - δ) v ∧
      ScalarRangeOn C R (fun x => u x - δ) ∧
      x0 ∈ closure C ∧
      v x0 < u x0 - δ ∧
      UpperSemicontinuousOn (fun x => u x - δ) (closure C) ∧
      LowerSemicontinuousOn v (closure C) ∧
      Tendsto x atTop (nhdsWithin x0 (closure C)) ∧
      Tendsto y atTop (nhdsWithin x0 (closure C)) ∧
      (∀ᶠ i in atTop,
        0 < α i ∧ x i ∈ closure C ∧ y i ∈ closure C ∧
          IsMaxOn
            (fun q : DoubledPoint n =>
              doubledObjective (fun z : Point n => u z - δ) v (α i) q)
            (closure C ×ˢ closure C) (x i, y i)) ∧
      Tendsto α atTop atTop

/--
Natural-number indexed constant-shift strictification data with scalar range
and shifted Ishii hypotheses derived from unshifted hypotheses.

In quantified mathematical form, suppose:

* `u x ∈ R` for every `x ∈ C`;
* if `r ∈ R` and `0 ≤ δ`, then `r - δ ∈ R`;
* the quadratic-penalty Ishii lemma holds on `C × C` for `u` and `v`;
* for every `η > 0` there exist real numbers `δ` and `ε` and functions
  `α : ℕ -> ℝ`, `x y : ℕ -> ℝ^n` such that `0 < δ`, `δ ≤ η`,
  `0 < ε`, `UniformScalarDecreaseOn C F δ ε` holds, and
  `StrictDoubledVariableLocalizationAlongOn C R (fun x => u x - δ) v atTop α x y`
  holds.

Then `ConstantShiftLocalizedStrictificationAlongDataOn C R F u v` holds.
-/
theorem constantShiftLocalizedStrictificationAlongDataOn_of_core_unshiftedIshii
    {C : Set (Point n)} {R : Set Real} {F : Operator n} {u v : Point n -> Real}
    (huR : ScalarRangeOn C R u) (hR : ClosedUnderSubNonneg R)
    (hIshii : QuadraticPenaltyIshiiLemmaOn C C u v)
    (hcore :
      ∀ η : Real, 0 < η ->
        ∃ δ : Real, ∃ ε : Real,
        ∃ α : ℕ -> Real, ∃ x : ℕ -> Point n, ∃ y : ℕ -> Point n,
          0 < δ ∧ δ <= η ∧ 0 < ε ∧
          UniformScalarDecreaseOn C F δ ε ∧
          StrictDoubledVariableLocalizationAlongOn C R (fun x => u x - δ) v atTop α x y) :
    ConstantShiftLocalizedStrictificationAlongDataOn C R F u v := by
  intro η hη
  rcases hcore η hη with ⟨δ, ε, α, x, y, hδpos, hδη, hε, hdec, hloc⟩
  exact
    ⟨δ, ε, α, x, y, hδpos, hδη, hε, hdec, hIshii.sub_const_left,
      huR.sub_const_of_closedUnderSubNonneg hR hδpos.le, hloc⟩

/--
Natural-number indexed constant-shift data give localized strictification in
the filter form.

In quantified mathematical form, if `u` is a viscosity subsolution on `C` and
for every `η > 0` the natural-number indexed constant-shift data above are
available, then `LocalizedStrictificationAlongOn C R F u v` holds, with
strictified functions of the form `x ↦ u x - δ`.
-/
theorem localizedStrictificationAlongOn_of_constantShiftData
    {C : Set (Point n)} {R : Set Real} {F : Operator n} {u v : Point n -> Real}
    (hu : ViscositySubsolution C F u)
    (hdata : ConstantShiftLocalizedStrictificationAlongDataOn C R F u v) :
    LocalizedStrictificationAlongOn C R F u v := by
  intro η hη
  rcases hdata η hη with
    ⟨δ, ε, α, x, y, hδpos, hδη, hε, hdec, hIshii, hR, hloc⟩
  refine ⟨ε, fun z => u z - δ, α, x, y, hε, hIshii, ?_, hR, hloc, ?_⟩
  · exact hu.strict_sub_const_of_uniformScalarDecrease hdec
  · intro z _hz
    linarith

/--
A constructor for natural-number indexed constant-shift localized
strictification data from the ordinary boundary-value comparison hypotheses.

In quantified mathematical form, this predicate says that, whenever `C` is
nonempty and `u`, `v` satisfy the boundary comparison, scalar-range,
compact-closure, subsolution, and supersolution hypotheses on `C`, then the
natural-number indexed constant-shift data in
`ConstantShiftLocalizedStrictificationAlongDataOn C R F u v` hold.
-/
def ConstantShiftBoundaryStrictificationAlongDataConstructorOn
    (C : Set (Point n)) (R : Set Real) (F : Operator n) : Prop :=
  ∀ u v : Point n -> Real,
    C.Nonempty ->
    BoundaryComparisonOn C u v ->
    ScalarRangeOn C R u ->
    CompactClosure C ->
    ViscositySubsolution C F u ->
    ViscositySupersolution C F v ->
      ConstantShiftLocalizedStrictificationAlongDataOn C R F u v

/--
A constructor for constant-shift data stated in terms of maximizers selected
on `closure C × closure C`.

In quantified mathematical form, this predicate says that, whenever `C` is
nonempty and `u`, `v` satisfy the boundary comparison, scalar-range,
compact-closure, subsolution, and supersolution hypotheses on `C`, then
`ConstantShiftClosureMaximizerDataOn C R F u v` holds.
-/
def ConstantShiftBoundaryClosureMaximizerDataConstructorOn
    (C : Set (Point n)) (R : Set Real) (F : Operator n) : Prop :=
  ∀ u v : Point n -> Real,
    C.Nonempty ->
    BoundaryComparisonOn C u v ->
    ScalarRangeOn C R u ->
    CompactClosure C ->
    ViscositySubsolution C F u ->
    ViscositySupersolution C F v ->
      ConstantShiftClosureMaximizerDataOn C R F u v

/--
The theorem-form hypothesis that supplies the quadratic-penalty Ishii lemma
on one spatial set.

In quantified mathematical form, this says: for every pair of functions
`u`, `v`, if `u` is upper semicontinuous on `C` and `v` is lower
semicontinuous on `C`, then `QuadraticPenaltyIshiiLemmaOn C C u v` holds.
-/
def QuadraticPenaltyIshiiLemmaConstructorOn
    (C : Set (Point n)) : Prop :=
  ∀ u v : Point n -> Real,
    UpperSemicontinuousOn u C ->
    LowerSemicontinuousOn v C ->
      QuadraticPenaltyIshiiLemmaOn C C u v

/--
The localized Jensen and Aleksandrov analytic inputs supply the
quadratic-penalty Ishii lemma constructor on a locally compact set.

In quantified mathematical form, if the relative topology on `C` is locally
compact, then for every upper semicontinuous `u` on `C` and every lower
semicontinuous `v` on `C`, the quadratic-penalty Ishii lemma holds on
`C × C`, provided the localized Jensen contact-set theorem and localized
Aleksandrov second-differentiability theorem are available in dimension
`n + n`.
-/
theorem QuadraticPenaltyIshiiLemmaConstructorOn.of_localized_jensen_aleksandrov
    (hJensen : JensenContactSetPositiveMeasureOnClosedBallTheorem (n + n))
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem (n + n))
    {C : Set (Point n)} [LocallyCompactSpace C] :
    QuadraticPenaltyIshiiLemmaConstructorOn C := by
  intro u v hu hv
  exact QuadraticPenaltyIshiiLemmaOn.of_localized_jensen_aleksandrov
    (n := n) hJensen hAleksandrov hu hv

/--
The quadratic-penalty Ishii lemma constructor follows from the localized
Aleksandrov second-differentiability theorem in dimension `n + n`, because
the localized Jensen contact-set theorem has already been proved.
-/
theorem QuadraticPenaltyIshiiLemmaConstructorOn.of_aleksandrov
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem (n + n))
    {C : Set (Point n)} [LocallyCompactSpace C] :
    QuadraticPenaltyIshiiLemmaConstructorOn C := by
  intro u v hu hv
  exact QuadraticPenaltyIshiiLemmaOn.of_aleksandrov
    (n := n) hAleksandrov hu hv

/--
The remaining constant-shift construction after scalar range and Ishii's
lemma have been separated out.

In quantified mathematical form, this predicate says that, whenever `C` is
nonempty and `u`, `v` satisfy the boundary comparison, scalar-range,
compact-closure, subsolution, and supersolution hypotheses on `C`, then for
every `η > 0` there exist real numbers `δ`, `ε` and sequences
`α : ℕ -> ℝ`, `x y : ℕ -> ℝ^n` such that:

* `0 < δ` and `δ ≤ η`;
* `0 < ε`;
* `UniformScalarDecreaseOn C F δ ε` holds;
* `StrictDoubledVariableLocalizationAlongOn C R (fun z => u z - δ) v atTop α x y`
  holds.
-/
def ConstantShiftBoundaryStrictificationAlongCoreConstructorOn
    (C : Set (Point n)) (R : Set Real) (F : Operator n) : Prop :=
  ∀ u v : Point n -> Real,
    C.Nonempty ->
    BoundaryComparisonOn C u v ->
    ScalarRangeOn C R u ->
    CompactClosure C ->
    ViscositySubsolution C F u ->
    ViscositySupersolution C F v ->
      ∀ η : Real, 0 < η ->
        ∃ δ : Real, ∃ ε : Real,
        ∃ α : ℕ -> Real, ∃ x : ℕ -> Point n, ∃ y : ℕ -> Point n,
          0 < δ ∧ δ <= η ∧ 0 < ε ∧
          UniformScalarDecreaseOn C F δ ε ∧
          StrictDoubledVariableLocalizationAlongOn C R (fun z => u z - δ) v atTop α x y

/--
The remaining trace-form constant-shift construction after the positive
zeroth-order lower bound has supplied the strict subsolution margin.

In quantified mathematical form, this predicate says that, whenever `C` is
nonempty and `u`, `v` satisfy the boundary comparison, scalar-range,
compact-closure, subsolution, and supersolution hypotheses for
`traceSecondOrderOperator A b c f` on `C`, then for every `η > 0` there
exist `δ > 0` and sequences `α : ℕ -> ℝ`, `x y : ℕ -> ℝ^n` such that
`δ ≤ η` and

`StrictDoubledVariableLocalizationAlongOn C R (fun z => u z - δ) v atTop α x y`

holds.
-/
def TraceConstantShiftBoundaryLocalizationAlongConstructorOn
    (C : Set (Point n)) (R : Set Real)
    (A : Point n -> Hessian n) (b : Point n -> Point n)
    (c f : Point n -> Real) : Prop :=
  ∀ u v : Point n -> Real,
    C.Nonempty ->
    BoundaryComparisonOn C u v ->
    ScalarRangeOn C R u ->
    CompactClosure C ->
    ViscositySubsolution C (traceSecondOrderOperator A b c f) u ->
    ViscositySupersolution C (traceSecondOrderOperator A b c f) v ->
      ∀ η : Real, 0 < η ->
        ∃ δ : Real,
        ∃ α : ℕ -> Real, ∃ x : ℕ -> Point n, ∃ y : ℕ -> Point n,
          0 < δ ∧ δ <= η ∧
          StrictDoubledVariableLocalizationAlongOn C R (fun z => u z - δ) v atTop α x y

/--
The trace-form constant-shift construction stated directly in terms of
maximizers selected on `closure C × closure C`.

In quantified mathematical form, this predicate says that, whenever `C` is
nonempty and `u`, `v` satisfy the boundary comparison, scalar-range,
compact-closure, subsolution, and supersolution hypotheses for
`traceSecondOrderOperator A b c f` on `C`, then for every `η > 0` there
exist `δ > 0`, sequences `α : ℕ -> ℝ`, `x y : ℕ -> ℝ^n`, and a point
`x0 : ℝ^n` such that:

* `δ ≤ η`;
* `x0 ∈ closure C` and `v x0 < u x0 - δ`;
* `x ↦ u x - δ` is upper semicontinuous on `closure C`;
* `v` is lower semicontinuous on `closure C`;
* `x i -> x0` and `y i -> x0` within `closure C` as `i -> ∞`;
* for all `i` in a set belonging to `atTop`, `(x i, y i)` maximizes
  `(x', y') ↦ u x' - δ - v y' - (α i / 2) * ∑ j, (x' j - y' j)^2`
  on `closure C × closure C`, with `0 < α i`, `x i ∈ closure C`, and
  `y i ∈ closure C`;
* `α i -> +∞` as `i -> ∞`.

The shifted scalar range, shifted Ishii lemma, and strict scalar decrease are
supplied separately by `ClosedUnderSubNonneg R`,
`QuadraticPenaltyIshiiLemmaConstructorOn C`, and a positive lower bound for
the zeroth-order coefficient.
-/
def TraceConstantShiftBoundaryClosureMaximizerConstructorOn
    (C : Set (Point n)) (R : Set Real)
    (A : Point n -> Hessian n) (b : Point n -> Point n)
    (c f : Point n -> Real) : Prop :=
  ∀ u v : Point n -> Real,
    C.Nonempty ->
    BoundaryComparisonOn C u v ->
    ScalarRangeOn C R u ->
    CompactClosure C ->
    ViscositySubsolution C (traceSecondOrderOperator A b c f) u ->
    ViscositySupersolution C (traceSecondOrderOperator A b c f) v ->
      ∀ η : Real, 0 < η ->
        ∃ δ : Real,
        ∃ α : ℕ -> Real, ∃ x : ℕ -> Point n, ∃ y : ℕ -> Point n,
        ∃ x0 : Point n,
          0 < δ ∧ δ <= η ∧
          x0 ∈ closure C ∧
          v x0 < u x0 - δ ∧
          UpperSemicontinuousOn (fun z => u z - δ) (closure C) ∧
          LowerSemicontinuousOn v (closure C) ∧
          Tendsto x atTop (nhdsWithin x0 (closure C)) ∧
          Tendsto y atTop (nhdsWithin x0 (closure C)) ∧
          (∀ᶠ i in atTop,
            0 < α i ∧ x i ∈ closure C ∧ y i ∈ closure C ∧
              IsMaxOn
                (fun q : DoubledPoint n =>
                  doubledObjective (fun z => u z - δ) v (α i) q)
                (closure C ×ˢ closure C) (x i, y i)) ∧
          Tendsto α atTop atTop

/--
For trace-form operators, a positive lower bound on the zeroth-order
coefficient reduces the constant-shift core constructor to the remaining
doubled-variable localization construction.

In quantified mathematical form, assume `0 < γ`, `γ ≤ c x` for every
`x ∈ C`, and
`TraceConstantShiftBoundaryLocalizationAlongConstructorOn C R A b c f`.
Then `ConstantShiftBoundaryStrictificationAlongCoreConstructorOn C R
(traceSecondOrderOperator A b c f)` holds.
-/
theorem constantShiftBoundaryStrictificationAlongCoreConstructorOn_traceSecondOrderOperator
    {C : Set (Point n)} {R : Set Real}
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    {γ : Real}
    (hγ : 0 < γ) (hcγ : ZerothCoefficientLowerBoundOn C c γ)
    (hconstruct : TraceConstantShiftBoundaryLocalizationAlongConstructorOn C R A b c f) :
    ConstantShiftBoundaryStrictificationAlongCoreConstructorOn C R
      (traceSecondOrderOperator A b c f) := by
  intro u v hCne hboundary huR hCcompact hu hv η hη
  rcases hconstruct u v hCne hboundary huR hCcompact hu hv η hη with
    ⟨δ, α, x, y, hδpos, hδη, hloc⟩
  refine ⟨δ, γ * δ, α, x, y, hδpos, hδη, ?_, ?_, hloc⟩
  · exact mul_pos hγ hδpos
  · exact
      uniformScalarDecreaseOn_traceSecondOrderOperator_of_zeroth_lower_bound
        hδpos.le hcγ

/--
For trace-form operators, the closure-maximizer construction, together with
the scalar-range and Ishii declarations and a positive lower bound for the
zeroth-order coefficient, gives the generic closure-maximizer data
constructor.
-/
theorem constantShiftBoundaryClosureMaximizerDataConstructorOn_traceSecondOrderOperator
    {C : Set (Point n)} {R : Set Real}
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    {γ : Real}
    (hR : ClosedUnderSubNonneg R)
    (hIshii : QuadraticPenaltyIshiiLemmaConstructorOn C)
    (hγ : 0 < γ) (hcγ : ZerothCoefficientLowerBoundOn C c γ)
    (hconstruct : TraceConstantShiftBoundaryClosureMaximizerConstructorOn C R A b c f) :
    ConstantShiftBoundaryClosureMaximizerDataConstructorOn C R
      (traceSecondOrderOperator A b c f) := by
  intro u v hCne hboundary huR hCcompact hu hv η hη
  rcases hconstruct u v hCne hboundary huR hCcompact hu hv η hη with
    ⟨δ, α, x, y, x0, hδpos, hδη, hx0closure, hgap, husc, hvlsc, hx, hy, hmax,
      hα⟩
  refine ⟨δ, γ * δ, α, x, y, x0, hδpos, hδη, ?_, ?_, ?_, ?_, hx0closure,
    hgap, husc, hvlsc, hx, hy, hmax, hα⟩
  · exact mul_pos hγ hδpos
  · exact
      uniformScalarDecreaseOn_traceSecondOrderOperator_of_zeroth_lower_bound
        hδpos.le hcγ
  · exact hIshii (fun z : Point n => u z - δ) v
      (hu.1.add upperSemicontinuousOn_const) hv.1
  · exact huR.sub_const_of_closedUnderSubNonneg hR hδpos.le

/--
The reduced boundary-level constant-shift construction implies the
constant-shift strictification data constructor.

In quantified mathematical form, assume:

* if `r ∈ R` and `δ ≥ 0`, then `r - δ ∈ R`;
* the quadratic-penalty Ishii lemma holds on `C × C` for every upper
  semicontinuous `u` and lower semicontinuous `v`;
* the remaining constant-shift construction in
  `ConstantShiftBoundaryStrictificationAlongCoreConstructorOn C R F` holds.

Then the full natural-number indexed constant-shift strictification data are
available for every pair satisfying the ordinary boundary-value hypotheses.
-/
theorem constantShiftBoundaryStrictificationAlongDataConstructorOn_of_coreConstructor
    {C : Set (Point n)} {R : Set Real} {F : Operator n}
    (hR : ClosedUnderSubNonneg R)
    (hIshii : QuadraticPenaltyIshiiLemmaConstructorOn C)
    (hconstruct : ConstantShiftBoundaryStrictificationAlongCoreConstructorOn C R F) :
    ConstantShiftBoundaryStrictificationAlongDataConstructorOn C R F := by
  intro u v hCne hboundary huR hCcompact hu hv
  exact constantShiftLocalizedStrictificationAlongDataOn_of_core_unshiftedIshii
    huR hR (hIshii u v hu.1 hv.1)
    (hconstruct u v hCne hboundary huR hCcompact hu hv)

/--
A constructor for natural-number indexed localized strictification from the
ordinary boundary-value comparison hypotheses.

In quantified mathematical form, this predicate says that, whenever `C` is
nonempty and `u`, `v` satisfy the boundary comparison, scalar-range,
compact-closure, subsolution, and supersolution hypotheses on `C`, then
`LocalizedStrictificationAlongOn C R F u v` holds.
-/
def LocalizedBoundaryStrictificationAlongConstructorOn
    (C : Set (Point n)) (R : Set Real) (F : Operator n) : Prop :=
  ∀ u v : Point n -> Real,
    C.Nonempty ->
    BoundaryComparisonOn C u v ->
    ScalarRangeOn C R u ->
    CompactClosure C ->
    ViscositySubsolution C F u ->
    ViscositySupersolution C F v ->
      LocalizedStrictificationAlongOn C R F u v

/--
Natural-number indexed constant-shift boundary data construct
natural-number indexed localized strictification from the ordinary
boundary-value hypotheses.
-/
theorem localizedBoundaryStrictificationAlongConstructorOn_of_constantShiftDataConstructor
    {C : Set (Point n)} {R : Set Real} {F : Operator n}
    (hconstruct : ConstantShiftBoundaryStrictificationAlongDataConstructorOn C R F) :
    LocalizedBoundaryStrictificationAlongConstructorOn C R F := by
  intro u v hCne hboundary huR hCcompact hu hv
  exact localizedStrictificationAlongOn_of_constantShiftData hu
    (hconstruct u v hCne hboundary huR hCcompact hu hv)

/--
Boundary comparison hypotheses together with the additional data needed to
apply compact-closure strictification.

In quantified mathematical form, this predicate consists of:

* `C` is nonempty;
* `u x ≤ v x` for every `x ∈ frontier C`;
* `u x ∈ R` for every `x ∈ C`;
* `closure C` is compact;
* `v` is a viscosity supersolution on `closure C`;
* `CompactClosureStrictificationOn C R F u v`.

The last condition is the remaining analytic bridge from the non-strict
subsolution hypothesis to strict comparison on `closure C`.
-/
def StrictifiedBoundaryComparisonHypothesesOn
    (C : Set (Point n)) (R : Set Real) (F : Operator n)
    (u v : Point n -> Real) : Prop :=
  C.Nonempty ∧
    BoundaryComparisonOn C u v ∧
    ScalarRangeOn C R u ∧
    CompactClosure C ∧
    ViscositySupersolution (closure C) F v ∧
    CompactClosureStrictificationOn C R F u v

/--
The theorem-shaped proposition for boundary comparison after strictification
has been supplied.

In quantified mathematical form, this says: if `F` is proper, continuous, and
satisfies the Ishii structural condition on `closure C` and `R`, then every
pair of functions satisfying `StrictifiedBoundaryComparisonHypothesesOn`
satisfies `u x ≤ v x` for every `x ∈ C`.
-/
def StrictifiedBoundaryComparisonStatementOn
    (C : Set (Point n)) (R : Set Real) (F : Operator n) : Prop :=
  Proper F ->
  OperatorContinuous F ->
  IshiiOperatorComparisonConditionOn (closure C) R F ->
  ∀ u v : Point n -> Real,
    StrictifiedBoundaryComparisonHypothesesOn C R F u v ->
      ComparisonConclusionOn C u v

/--
Boundary comparison statement whose structural condition is stated on
`closure C`.

In quantified mathematical form, this says: under properness, operator
continuity, `IshiiOperatorComparisonConditionOn (closure C) R F`, boundary
comparison on `frontier C`, the scalar-range condition on `C`, compactness of
`closure C`, and the non-strict viscosity subsolution and supersolution
hypotheses on `C`, one has `u x ≤ v x` for every `x ∈ C`.
-/
def CompactClosureBoundaryComparisonStatementOn
    (C : Set (Point n)) (R : Set Real) (F : Operator n) : Prop :=
  Proper F ->
  OperatorContinuous F ->
  IshiiOperatorComparisonConditionOn (closure C) R F ->
  ∀ u v : Point n -> Real,
    BoundaryComparisonOn C u v ->
    ScalarRangeOn C R u ->
    CompactClosure C ->
    ViscositySubsolution C F u ->
    ViscositySupersolution C F v ->
      ComparisonConclusionOn C u v

/--
A constructor for the strictified boundary hypotheses from the ordinary
boundary-value comparison hypotheses.

In quantified mathematical form, this predicate says that, whenever `C` is
nonempty and `u`, `v` satisfy the boundary comparison, scalar-range,
compact-closure, subsolution, and supersolution hypotheses on `C`, then the
strictified hypotheses needed by `StrictifiedBoundaryComparisonStatementOn`
hold.
-/
def CompactClosureBoundaryStrictificationConstructorOn
    (C : Set (Point n)) (R : Set Real) (F : Operator n) : Prop :=
  ∀ u v : Point n -> Real,
    C.Nonempty ->
    BoundaryComparisonOn C u v ->
    ScalarRangeOn C R u ->
    CompactClosure C ->
    ViscositySubsolution C F u ->
    ViscositySupersolution C F v ->
      StrictifiedBoundaryComparisonHypothesesOn C R F u v

/--
Reduced constructor for the analytic data in the strictified boundary
hypotheses.

In quantified mathematical form, this says that, under the ordinary
boundary-value hypotheses on `C`, one can prove both:

* `v` is a viscosity supersolution on `closure C`;
* `CompactClosureStrictificationOn C R F u v`.

Together with the ordinary boundary comparison, scalar-range, compactness,
and nonemptiness hypotheses, these two conclusions imply
`StrictifiedBoundaryComparisonHypothesesOn C R F u v`.
-/
def CompactClosureStrictificationDataConstructorOn
    (C : Set (Point n)) (R : Set Real) (F : Operator n) : Prop :=
  ∀ u v : Point n -> Real,
    C.Nonempty ->
    BoundaryComparisonOn C u v ->
    ScalarRangeOn C R u ->
    CompactClosure C ->
    ViscositySubsolution C F u ->
    ViscositySupersolution C F v ->
      ViscositySupersolution (closure C) F v ∧
        CompactClosureStrictificationOn C R F u v

/--
The reduced analytic data constructor supplies the full strictified boundary
hypotheses.
-/
theorem compactClosureBoundaryStrictificationConstructorOn_of_dataConstructor
    {C : Set (Point n)} {R : Set Real} {F : Operator n}
    (hdata : CompactClosureStrictificationDataConstructorOn C R F) :
    CompactClosureBoundaryStrictificationConstructorOn C R F := by
  intro u v hCne hboundary huR hCcompact hu hv
  rcases hdata u v hCne hboundary huR hCcompact hu hv with
    ⟨hvClosure, hstrictify⟩
  exact ⟨hCne, hboundary, huR, hCcompact, hvClosure, hstrictify⟩

/--
The theorem-shaped proposition for strict comparison conditional on Ishii's
lemma.

In quantified mathematical form, this says: assume `F` is proper, continuous,
and satisfies `IshiiOperatorComparisonConditionOn C R F`. Let `ε > 0`. For
every pair of functions `u`, `v`, assume:

* the additional hypotheses `extraHypotheses u v`;
* `QuadraticPenaltyIshiiLemmaOn C C u v`;
* `u` is a strict viscosity subsolution with margin `ε`;
* `v` is a viscosity supersolution;
* `u x ∈ R` for every `x ∈ C`.

Then `u x ≤ v x` for every `x ∈ C`.
-/
def StrictProperComparisonStatementOn
    (C : Set (Point n)) (R : Set Real) (F : Operator n)
    (extraHypotheses : (Point n -> Real) -> (Point n -> Real) -> Prop) : Prop :=
  Proper F ->
  OperatorContinuous F ->
  IshiiOperatorComparisonConditionOn C R F ->
  ∀ ε : Real, 0 < ε ->
  ∀ u v : Point n -> Real,
    extraHypotheses u v ->
    QuadraticPenaltyIshiiLemmaOn C C u v ->
    StrictViscositySubsolution C F ε u ->
    ViscositySupersolution C F v ->
    ScalarRangeOn C R u ->
      ComparisonConclusionOn C u v

/--
Compactness hypotheses for strict comparison on a fixed set `C`.

In quantified mathematical form, this predicate says that `C` is nonempty and
compact. It does not impose any additional condition on the particular
functions `u` and `v`.
-/
def CompactStrictComparisonHypothesesOn
    (C : Set (Point n)) (_u _v : Point n -> Real) : Prop :=
  C.Nonempty ∧ IsCompact C

end ViscositySolns
