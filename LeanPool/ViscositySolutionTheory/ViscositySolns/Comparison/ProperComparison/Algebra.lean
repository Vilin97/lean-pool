/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Comparison.ProperComparison.Setup

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Algebraic comparison consequences after Ishii's lemma.
-/

@[expose] public noncomputable section

open Filter
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
If the quadratic-penalty conclusion of Ishii's lemma holds at `(x, y)`, then
the corresponding closed superjet and closed subjet produce the viscosity
inequalities for the same first-derivative vector `α • (x - y)`.
-/
theorem exists_closedSemijet_inequalities_of_quadraticPenaltyIshiiConclusion
    {C : Set (Point n)} {F : Operator n} {u v : Point n -> Real}
    {α : Real} {x y : Point n}
    (hu : ViscositySubsolution C F u) (hv : ViscositySupersolution C F v)
    (hF : OperatorContinuous F)
    (hI : QuadraticPenaltyIshiiConclusion C C u v α x y) :
    ∃ X Y : Hessian n,
      ({ gradient := quadraticPenaltyGradientLeft α x y, hessian := X } : Jet n) ∈
        ClosedSuperjet C u x ∧
      ({ gradient := quadraticPenaltyGradientLeft α x y, hessian := Y } : Jet n) ∈
        ClosedSubjet C v y ∧
      IshiiMatrixRelation α x y X Y ∧
      F x (u x) (quadraticPenaltyGradientLeft α x y) X <= 0 ∧
      0 <= F y (v y) (quadraticPenaltyGradientLeft α x y) Y := by
  rcases hI with ⟨data⟩
  refine ⟨data.X, data.Y, data.superjet_mem, ?_, data.matrix_relation, ?_, ?_⟩
  · simpa using data.subjet_mem
  · exact hu.closedSuperjet_le_of_operatorContinuous hF data.superjet_mem
  · simpa using hv.closedSubjet_nonneg_of_operatorContinuous hF data.subjet_mem

/--
Assume the conclusion of Ishii's lemma at `(x, y)`. If `v y ≤ u x`, then
properness implies that the operator gap

`F y (u x) (α • (x - y)) Y - F x (u x) (α • (x - y)) X`

is nonnegative for the matrices supplied by the closed semijets.
-/
theorem exists_nonnegative_operator_gap_of_quadraticPenaltyIshiiConclusion
    {C : Set (Point n)} {F : Operator n} {u v : Point n -> Real}
    {α : Real} {x y : Point n}
    (hu : ViscositySubsolution C F u) (hv : ViscositySupersolution C F v)
    (hF : OperatorContinuous F) (hproper : Proper F)
    (hvyux : v y <= u x)
    (hI : QuadraticPenaltyIshiiConclusion C C u v α x y) :
    ∃ X Y : Hessian n,
      IshiiMatrixRelation α x y X Y ∧
      0 <=
        F y (u x) (quadraticPenaltyGradientLeft α x y) Y -
          F x (u x) (quadraticPenaltyGradientLeft α x y) X := by
  rcases exists_closedSemijet_inequalities_of_quadraticPenaltyIshiiConclusion
    hu hv hF hI with ⟨X, Y, _hJX, _hJY, hXY, hsub, hsuper⟩
  refine ⟨X, Y, hXY, ?_⟩
  have hmono :
      F y (v y) (quadraticPenaltyGradientLeft α x y) Y <=
        F y (u x) (quadraticPenaltyGradientLeft α x y) Y :=
    hproper.mono_value y (quadraticPenaltyGradientLeft α x y) Y hvyux
  linarith

/--
Under the specialized structural condition, the same operator gap is bounded
above by a comparison modulus. Thus the matrices supplied by Ishii's lemma
satisfy both inequalities

`0 ≤ gap` and
`gap ≤ ω (α * ‖x - y‖ ^ 2 + ‖x - y‖)`.
-/
theorem exists_operator_gap_bounds_of_quadraticPenaltyIshiiConclusion
    {C : Set (Point n)} {R : Set Real} {F : Operator n} {u v : Point n -> Real}
    {α : Real} {x y : Point n}
    (hu : ViscositySubsolution C F u) (hv : ViscositySupersolution C F v)
    (hFcont : OperatorContinuous F) (hproper : Proper F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hα : 0 < α) (hx : x ∈ C) (hy : y ∈ C) (hr : u x ∈ R)
    (hvyux : v y <= u x)
    (hI : QuadraticPenaltyIshiiConclusion C C u v α x y) :
    ∃ ω : Real -> Real, ComparisonModulus ω ∧
      ∃ X Y : Hessian n,
        IshiiMatrixRelation α x y X Y ∧
        0 <=
          F y (u x) (quadraticPenaltyGradientLeft α x y) Y -
            F x (u x) (quadraticPenaltyGradientLeft α x y) X ∧
        F y (u x) (quadraticPenaltyGradientLeft α x y) Y -
            F x (u x) (quadraticPenaltyGradientLeft α x y) X <=
          ω (α * ‖x - y‖ ^ 2 + ‖x - y‖) := by
  rcases hcomp.bound with ⟨ω, hω, hbound⟩
  rcases exists_nonnegative_operator_gap_of_quadraticPenaltyIshiiConclusion
    hu hv hFcont hproper hvyux hI with ⟨X, Y, hXY, hnonneg⟩
  refine ⟨ω, hω, X, Y, hXY, hnonneg, ?_⟩
  exact hbound α hα x hx y hy (u x) hr X Y hXY

/--
Assume the conclusion of Ishii's lemma at `(x, y)`. If `u` is a strict
subsolution with margin `ε` and `v y ≤ u x`, then properness implies that the
operator gap

`F y (u x) (α • (x - y)) Y - F x (u x) (α • (x - y)) X`

is at least `ε` for the matrices supplied by the closed semijets.
-/
theorem exists_strict_operator_gap_of_quadraticPenaltyIshiiConclusion
    {C : Set (Point n)} {F : Operator n} {u v : Point n -> Real}
    {ε α : Real} {x y : Point n}
    (hu : StrictViscositySubsolution C F ε u) (hv : ViscositySupersolution C F v)
    (hF : OperatorContinuous F) (hproper : Proper F)
    (hvyux : v y <= u x)
    (hI : QuadraticPenaltyIshiiConclusion C C u v α x y) :
    ∃ X Y : Hessian n,
      IshiiMatrixRelation α x y X Y ∧
      ε <=
        F y (u x) (quadraticPenaltyGradientLeft α x y) Y -
          F x (u x) (quadraticPenaltyGradientLeft α x y) X := by
  rcases hI with ⟨data⟩
  refine ⟨data.X, data.Y, data.matrix_relation, ?_⟩
  have hsub :
      F x (u x) (quadraticPenaltyGradientLeft α x y) data.X <= -ε :=
    hu.closedSuperjet_le_neg_of_operatorContinuous hF data.superjet_mem
  have hsuper :
      0 <= F y (v y) (quadraticPenaltyGradientLeft α x y) data.Y := by
    simpa using hv.closedSubjet_nonneg_of_operatorContinuous hF data.subjet_mem
  have hmono :
      F y (v y) (quadraticPenaltyGradientLeft α x y) data.Y <=
        F y (u x) (quadraticPenaltyGradientLeft α x y) data.Y :=
    hproper.mono_value y (quadraticPenaltyGradientLeft α x y) data.Y hvyux
  linarith

/--
Let `ε > 0`, let `u` be a strict subsolution with margin `ε`, and let `v` be
a supersolution. Assume properness, operator continuity, and
`QuadraticPenaltyIshiiLemmaOn C C u v`.

If, for all `i` in a set belonging to `l`, `α i > 0`, `x i ∈ C`, `y i ∈ C`,
`v (y i) ≤ u (x i)`, and `(x i, y i)` maximizes the doubled-variable
objective on `C × C`, then, for all `i` in a set belonging to `l`,

`0 < α i * ‖x i - y i‖ ^ 2 + ‖x i - y i‖`.

Indeed, if the displayed quantity were zero for one of these indices, then
`x i = y i`. Ishii's lemma would produce matrices `X` and `Y` with
`X ≤ Y`. Degenerate ellipticity would make the corresponding operator
difference nonpositive, contradicting the strict subsolution gap `ε > 0`.
-/
theorem eventually_comparisonScale_pos_of_strict_eventually_isMaxOn
    {ι : Type*} {l : Filter ι}
    {C : Set (Point n)} {F : Operator n} {u v : Point n -> Real}
    {ε : Real} {α : ι -> Real} {x y : ι -> Point n}
    (hu : StrictViscositySubsolution C F ε u)
    (hv : ViscositySupersolution C F v)
    (hFcont : OperatorContinuous F) (hproper : Proper F)
    (hIshii : QuadraticPenaltyIshiiLemmaOn C C u v)
    (hε : 0 < ε)
    (hdata :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧ v (y i) <= u (x i) ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
            (C ×ˢ C) (x i, y i)) :
    ∀ᶠ i in l, 0 < α i * ‖x i - y i‖ ^ 2 + ‖x i - y i‖ := by
  filter_upwards [hdata] with i hi
  rcases hi with ⟨hαi, hxC, hyC, hvyux, hmaxi⟩
  by_contra hnonpos
  have hscale_nonneg : 0 <= α i * ‖x i - y i‖ ^ 2 + ‖x i - y i‖ :=
    comparisonScale_nonneg hαi (x i) (y i)
  have hscale_eq : α i * ‖x i - y i‖ ^ 2 + ‖x i - y i‖ = 0 :=
    le_antisymm (le_of_not_gt hnonpos) hscale_nonneg
  have hnorm_eq : ‖x i - y i‖ = 0 := by
    have hnorm_nonneg : 0 <= ‖x i - y i‖ := norm_nonneg _
    have hquad_nonneg : 0 <= α i * ‖x i - y i‖ ^ 2 :=
      mul_nonneg hαi.le (sq_nonneg ‖x i - y i‖)
    nlinarith
  have hxy : x i = y i := by
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm_eq)
  have hlocal : HasQuadraticPenaltyLocalMaximumOn C C u v (α i) (x i) (y i) :=
    hasQuadraticPenaltyLocalMaximumOn_of_isMaxOn_doubledObjective
      (show (x i, y i) ∈ C ×ˢ C from ⟨hxC, hyC⟩) hmaxi
  have hI : QuadraticPenaltyIshiiConclusion C C u v (α i) (x i) (y i) :=
    hIshii (α i) hαi (x i) (y i) hlocal
  rcases exists_strict_operator_gap_of_quadraticPenaltyIshiiConclusion
    hu hv hFcont hproper hvyux hI with ⟨X, Y, hXY, hgap⟩
  have hXYle : X <= Y := hXY.left_le_right
  have hmono :
      F (x i) (u (x i)) 0 Y <= F (x i) (u (x i)) 0 X :=
    hproper.degenerateElliptic (x i) (u (x i)) 0 Y X hXYle
  have hgap_nonpos :
      F (y i) (u (x i)) (quadraticPenaltyGradientLeft (α i) (x i) (y i)) Y -
          F (x i) (u (x i)) (quadraticPenaltyGradientLeft (α i) (x i) (y i)) X <=
        0 := by
    have hgrad : quadraticPenaltyGradientLeft (α i) (x i) (x i) = 0 := by
      ext j
      simp [quadraticPenaltyGradientLeft]
    rw [← hxy]
    rw [hgrad]
    exact sub_nonpos.mpr hmono
  exact not_lt_of_ge (le_trans hgap hgap_nonpos) hε

/--
With a strict subsolution margin `ε`, the matrices supplied by Ishii's lemma
satisfy both inequalities

`ε ≤ gap` and
`gap ≤ ω (α * ‖x - y‖ ^ 2 + ‖x - y‖)`.
-/
theorem exists_strict_operator_gap_bounds_of_quadraticPenaltyIshiiConclusion
    {C : Set (Point n)} {R : Set Real} {F : Operator n} {u v : Point n -> Real}
    {ε α : Real} {x y : Point n}
    (hu : StrictViscositySubsolution C F ε u) (hv : ViscositySupersolution C F v)
    (hFcont : OperatorContinuous F) (hproper : Proper F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hα : 0 < α) (hx : x ∈ C) (hy : y ∈ C) (hr : u x ∈ R)
    (hvyux : v y <= u x)
    (hI : QuadraticPenaltyIshiiConclusion C C u v α x y) :
    ∃ ω : Real -> Real, ComparisonModulus ω ∧
      ∃ X Y : Hessian n,
        IshiiMatrixRelation α x y X Y ∧
        ε <=
          F y (u x) (quadraticPenaltyGradientLeft α x y) Y -
            F x (u x) (quadraticPenaltyGradientLeft α x y) X ∧
        F y (u x) (quadraticPenaltyGradientLeft α x y) Y -
            F x (u x) (quadraticPenaltyGradientLeft α x y) X <=
          ω (α * ‖x - y‖ ^ 2 + ‖x - y‖) := by
  rcases hcomp.bound with ⟨ω, hω, hbound⟩
  rcases exists_strict_operator_gap_of_quadraticPenaltyIshiiConclusion
    hu hv hFcont hproper hvyux hI with ⟨X, Y, hXY, hgap⟩
  refine ⟨ω, hω, X, Y, hXY, hgap, ?_⟩
  exact hbound α hα x hx y hy (u x) hr X Y hXY

/--
Let `ε > 0`, let `u` be a strict subsolution with margin `ε`, and let `v` be a
supersolution. Assume properness, operator continuity, the Ishii structural
condition, and `QuadraticPenaltyIshiiLemmaOn C C u v`.

Let `α i`, `x i`, and `y i` be data indexed by a nontrivial filter `l`.
Suppose that for all `i` in a set belonging to `l`:

* `α i > 0`;
* `x i ∈ C` and `y i ∈ C`;
* `u (x i) ∈ R`;
* `v (y i) ≤ u (x i)`;
* `(x i, y i)` maximizes
  `(x', y') ↦ u x' - v y' - (α i / 2) * ∑ j, (x' j - y' j)^2`
  on `C × C`.

Then the associated scales
`α i * ‖x i - y i‖ ^ 2 + ‖x i - y i‖` cannot converge to `0` through positive
values along `l`.
-/
theorem not_eventually_strict_isMaxOn_doubledObjective_of_tendsto_scale
    {ι : Type*} {l : Filter ι} [NeBot l]
    {C : Set (Point n)} {R : Set Real} {F : Operator n} {u v : Point n -> Real}
    {ε : Real} {α : ι -> Real} {x y : ι -> Point n}
    (hu : StrictViscositySubsolution C F ε u) (hv : ViscositySupersolution C F v)
    (hFcont : OperatorContinuous F) (hproper : Proper F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hIshii : QuadraticPenaltyIshiiLemmaOn C C u v) (hε : 0 < ε)
    (hdata :
      ∀ᶠ i in l,
        0 < α i ∧ x i ∈ C ∧ y i ∈ C ∧ u (x i) ∈ R ∧ v (y i) <= u (x i) ∧
          IsMaxOn (fun q : DoubledPoint n => doubledObjective u v (α i) q)
            (C ×ˢ C) (x i, y i)) :
    ¬ Tendsto (fun i : ι => α i * ‖x i - y i‖ ^ 2 + ‖x i - y i‖)
        l (nhdsWithin 0 (Set.Ioi 0)) := by
  rcases hcomp.bound with ⟨ω, hω, hbound⟩
  intro hscale
  apply not_eventually_strict_le_modulus_of_tendsto_nhdsWithin_Ioi
    hω hε hscale
  filter_upwards [hdata] with i hi
  rcases hi with ⟨hα, hxC, hyC, hr, hvyux, hmax⟩
  have hlocal : HasQuadraticPenaltyLocalMaximumOn C C u v (α i) (x i) (y i) :=
    hasQuadraticPenaltyLocalMaximumOn_of_isMaxOn_doubledObjective
      (show (x i, y i) ∈ C ×ˢ C from ⟨hxC, hyC⟩) hmax
  have hI : QuadraticPenaltyIshiiConclusion C C u v (α i) (x i) (y i) :=
    hIshii (α i) hα (x i) (y i) hlocal
  rcases exists_strict_operator_gap_of_quadraticPenaltyIshiiConclusion
    hu hv hFcont hproper hvyux hI with ⟨X, Y, hXY, hgap⟩
  have hupper :
      F (y i) (u (x i)) (quadraticPenaltyGradientLeft (α i) (x i) (y i)) Y -
          F (x i) (u (x i)) (quadraticPenaltyGradientLeft (α i) (x i) (y i)) X <=
        ω (α i * ‖x i - y i‖ ^ 2 + ‖x i - y i‖) :=
    hbound (α i) hα (x i) hxC (y i) hyC (u (x i)) hr X Y hXY
  exact le_trans hgap hupper

/--
Strict comparison conditional on the filter form of the doubled-variable
localization hypothesis and on Ishii's lemma.

Assume `ε > 0`, `u` is a strict subsolution with margin `ε`, `v` is a
supersolution, `F` is proper and continuous, and `F` satisfies the Ishii
structural condition. Assume also `QuadraticPenaltyIshiiLemmaOn C C u v`.

If failure of `u ≤ v` somewhere on `C` produces doubled-variable maximum data
along a nontrivial filter whose scales tend to `0` through positive values,
then `u ≤ v` at every point of `C`.
-/
theorem strictComparison_of_doubledVariableLocalizationAlong
    {ι : Type*} {l : Filter ι} [NeBot l]
    {C : Set (Point n)} {R : Set Real} {F : Operator n} {u v : Point n -> Real}
    {ε : Real} {α : ι -> Real} {x y : ι -> Point n}
    (hu : StrictViscositySubsolution C F ε u) (hv : ViscositySupersolution C F v)
    (hFcont : OperatorContinuous F) (hproper : Proper F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hIshii : QuadraticPenaltyIshiiLemmaOn C C u v)
    (hε : 0 < ε)
    (hloc : StrictDoubledVariableLocalizationAlongOn C R u v l α x y) :
    ComparisonConclusionOn C u v := by
  intro z hz
  by_contra hnot
  have hfail : ∃ z : Point n, z ∈ C ∧ v z < u z := by
    exact ⟨z, hz, not_le.mp hnot⟩
  rcases hloc hfail with ⟨hdata, hscale⟩
  exact not_eventually_strict_isMaxOn_doubledObjective_of_tendsto_scale
    hu hv hFcont hproper hcomp hIshii hε hdata hscale

/--
Comparison from strictification and natural-number indexed doubled-variable
localization on `C`.

In quantified mathematical form, assume `F` is proper and continuous, assume
the Ishii structural condition on `C` and `R`, and assume that `v` is a
viscosity supersolution on `C`. If, for every `η > 0`, there are
`ε > 0`, a function `w`, and natural-number indexed selected
doubled-variable data satisfying the conclusions in
`LocalizedStrictificationAlongOn C R F u v`, then `u x ≤ v x` for every
`x ∈ C`.
-/
theorem comparison_of_localizedStrictificationAlong
    {C : Set (Point n)} {R : Set Real} {F : Operator n} {u v : Point n -> Real}
    (hproper : Proper F)
    (hFcont : OperatorContinuous F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hv : ViscositySupersolution C F v)
    (hstrictify : LocalizedStrictificationAlongOn C R F u v) :
    ComparisonConclusionOn C u v := by
  intro z hz
  refine le_of_forall_pos_le_add fun η hη => ?_
  rcases hstrictify η hη with
    ⟨ε, w, α, x, y, hε, hIshii, hw, hwR, hloc, huw⟩
  have hwv : ComparisonConclusionOn C w v :=
    strictComparison_of_doubledVariableLocalizationAlong
      (l := atTop) (α := α) (x := x) (y := y)
      hw hv hFcont hproper hcomp hIshii hε hloc
  have huzw : u z <= w z + η := huw z hz
  have hwzv : w z <= v z := hwv z hz
  linarith

/--
Natural-number indexed constant-shift data imply comparison for a fixed pair
of functions.

In quantified mathematical form, assume:

* `F` is proper and continuous;
* `F` satisfies `IshiiOperatorComparisonConditionOn C R F`;
* `u` is a viscosity subsolution of `F = 0` on `C`;
* `v` is a viscosity supersolution of `F = 0` on `C`;
* for every `η > 0`, there exist `δ > 0`, `ε > 0`, and sequences
  `α : ℕ -> ℝ`, `x y : ℕ -> ℝ^n` satisfying the conditions in
  `ConstantShiftLocalizedStrictificationAlongDataOn C R F u v`.

Then `u z ≤ v z` for every `z ∈ C`.
-/
theorem comparison_of_constantShiftLocalizedStrictificationAlongData
    {C : Set (Point n)} {R : Set Real} {F : Operator n} {u v : Point n -> Real}
    (hproper : Proper F)
    (hFcont : OperatorContinuous F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hu : ViscositySubsolution C F u)
    (hv : ViscositySupersolution C F v)
    (hdata : ConstantShiftLocalizedStrictificationAlongDataOn C R F u v) :
    ComparisonConclusionOn C u v :=
  comparison_of_localizedStrictificationAlong hproper hFcont hcomp hv
    (localizedStrictificationAlongOn_of_constantShiftData hu hdata)

/--
Reduced natural-number indexed constant-shift data imply comparison for a
fixed pair of functions.

In quantified mathematical form, suppose:

* `F` is proper and continuous;
* `F` satisfies `IshiiOperatorComparisonConditionOn C R F`;
* `u` is a viscosity subsolution of `F = 0` on `C`;
* `v` is a viscosity supersolution of `F = 0` on `C`;
* `u x ∈ R` for every `x ∈ C`;
* if `r ∈ R` and `δ ≥ 0`, then `r - δ ∈ R`;
* the quadratic-penalty Ishii lemma holds for `u` and `v` on `C × C`;
* for every `η > 0`, there exist `δ > 0`, `ε > 0`, and sequences
  `α : ℕ -> ℝ`, `x y : ℕ -> ℝ^n` such that `δ ≤ η`,
  `UniformScalarDecreaseOn C F δ ε` holds, and
  `StrictDoubledVariableLocalizationAlongOn C R (fun z => u z - δ) v atTop α x y`
  holds.

Then `u z ≤ v z` for every `z ∈ C`.
-/
theorem comparison_of_constantShiftLocalizedStrictificationAlongCore
    {C : Set (Point n)} {R : Set Real} {F : Operator n} {u v : Point n -> Real}
    (hproper : Proper F)
    (hFcont : OperatorContinuous F)
    (hcomp : IshiiOperatorComparisonConditionOn C R F)
    (hu : ViscositySubsolution C F u)
    (hv : ViscositySupersolution C F v)
    (huR : ScalarRangeOn C R u)
    (hR : ClosedUnderSubNonneg R)
    (hIshii : QuadraticPenaltyIshiiLemmaOn C C u v)
    (hcore :
      ∀ η : Real, 0 < η ->
        ∃ δ : Real, ∃ ε : Real,
        ∃ α : ℕ -> Real, ∃ x : ℕ -> Point n, ∃ y : ℕ -> Point n,
          0 < δ ∧ δ <= η ∧ 0 < ε ∧
          UniformScalarDecreaseOn C F δ ε ∧
          StrictDoubledVariableLocalizationAlongOn C R (fun z => u z - δ) v atTop α x y) :
    ComparisonConclusionOn C u v :=
  comparison_of_constantShiftLocalizedStrictificationAlongData
    hproper hFcont hcomp hu hv
    (constantShiftLocalizedStrictificationAlongDataOn_of_core_unshiftedIshii
      huR hR hIshii hcore)

/--
If the ordinary boundary-value hypotheses construct natural-number indexed
localized strictification, then the boundary comparison statement on `C`
follows.

In quantified mathematical form, assume `F` is proper and continuous and
satisfies the Ishii structural condition on `C` and `R`. If, whenever `C` is
nonempty and a pair `u`, `v` satisfies the ordinary boundary-value
hypotheses on `C`, those hypotheses imply
`LocalizedStrictificationAlongOn C R F u v`, then the ordinary boundary-value
hypotheses imply `u x ≤ v x` for every `x ∈ C`.
-/
theorem properBoundaryComparisonStatementOn_of_localizedStrictificationAlongConstructor
    {C : Set (Point n)} {R : Set Real} {F : Operator n}
    (hconstruct : LocalizedBoundaryStrictificationAlongConstructorOn C R F) :
    ProperBoundaryComparisonStatementOn C R F := by
  intro hproper hFcont hcomp u v hextra hu hv _huR
  rcases hextra with ⟨hboundary, huR, hCcompact⟩
  by_cases hCne : C.Nonempty
  · exact comparison_of_localizedStrictificationAlong hproper hFcont hcomp hv
      (hconstruct u v hCne hboundary huR hCcompact hu hv)
  · intro x hx
    exact (hCne ⟨x, hx⟩).elim

/--
Natural-number indexed constant-shift boundary data imply the ordinary
boundary comparison statement on `C`.
-/
theorem properBoundaryComparisonStatementOn_of_constantShiftAlongDataConstructor
    {C : Set (Point n)} {R : Set Real} {F : Operator n}
    (hconstruct : ConstantShiftBoundaryStrictificationAlongDataConstructorOn C R F) :
    ProperBoundaryComparisonStatementOn C R F :=
  properBoundaryComparisonStatementOn_of_localizedStrictificationAlongConstructor
    (localizedBoundaryStrictificationAlongConstructorOn_of_constantShiftDataConstructor
      hconstruct)

/--
The reduced boundary-level constant-shift construction implies the ordinary
boundary comparison statement.

In quantified mathematical form, assume:

* if `r ∈ R` and `δ ≥ 0`, then `r - δ ∈ R`;
* the quadratic-penalty Ishii lemma holds on `C × C` for every upper
  semicontinuous `u` and lower semicontinuous `v`;
* the remaining constant-shift construction in
  `ConstantShiftBoundaryStrictificationAlongCoreConstructorOn C R F` holds.

Then the ordinary boundary-value comparison target
`ProperBoundaryComparisonStatementOn C R F` follows.
-/
theorem properBoundaryComparisonStatementOn_of_constantShiftAlongCoreConstructor
    {C : Set (Point n)} {R : Set Real} {F : Operator n}
    (hR : ClosedUnderSubNonneg R)
    (hIshii : QuadraticPenaltyIshiiLemmaConstructorOn C)
    (hconstruct : ConstantShiftBoundaryStrictificationAlongCoreConstructorOn C R F) :
    ProperBoundaryComparisonStatementOn C R F :=
  properBoundaryComparisonStatementOn_of_constantShiftAlongDataConstructor
    (constantShiftBoundaryStrictificationAlongDataConstructorOn_of_coreConstructor
      hR hIshii hconstruct)

/--
Trace-form version of the reduced constant-shift boundary comparison
criterion.

In quantified mathematical form, assume:

* if `r ∈ R` and `δ ≥ 0`, then `r - δ ∈ R`;
* the quadratic-penalty Ishii lemma holds on `C × C` for every upper
  semicontinuous `u` and lower semicontinuous `v`;
* `0 < γ` and `γ ≤ c x` for every `x ∈ C`;
* the remaining trace-form localization construction in
  `TraceConstantShiftBoundaryLocalizationAlongConstructorOn C R A b c f`
  holds.

Then the ordinary boundary comparison target holds for
`traceSecondOrderOperator A b c f`.
-/
theorem properBoundaryComparisonStatementOn_traceSecondOrderOperator_of_constantShiftLocalization
    {C : Set (Point n)} {R : Set Real}
    {A : Point n -> Hessian n} {b : Point n -> Point n} {c f : Point n -> Real}
    {γ : Real}
    (hR : ClosedUnderSubNonneg R)
    (hIshii : QuadraticPenaltyIshiiLemmaConstructorOn C)
    (hγ : 0 < γ) (hcγ : ZerothCoefficientLowerBoundOn C c γ)
    (hconstruct : TraceConstantShiftBoundaryLocalizationAlongConstructorOn C R A b c f) :
    ProperBoundaryComparisonStatementOn C R (traceSecondOrderOperator A b c f) :=
  properBoundaryComparisonStatementOn_of_constantShiftAlongCoreConstructor
    hR hIshii
    (constantShiftBoundaryStrictificationAlongCoreConstructorOn_traceSecondOrderOperator
      hγ hcγ hconstruct)

end ViscositySolns
