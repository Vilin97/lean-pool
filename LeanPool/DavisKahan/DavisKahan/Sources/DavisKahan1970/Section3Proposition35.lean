/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.Proposition35Exponential
import LeanPool.DavisKahan.ForTauCeti.Analysis.RCLike.ScalarTransportFunctionalCalculus

/-! # Section3Proposition35 -/

open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan 1970, Proposition 3.5, in arbitrary Hilbert dimension

This file is the paper-facing surface for Proposition 3.5, for closed subspaces of a real or
complex Hilbert space, without a finite-dimensional hypothesis.

**The proposition is not acute throughout, and the three clauses do not share a scope.**  The
source reads: "`Θ` commutes with `P`, with `Q`, with `J`, and with `U`.  For every eigenvalue
`θ`, the eigenvectors `x` satisfy `∠(x, Ux) = θ`.  *In the acute case*, for every eigenvalue
`θ`, the eigenspace `Ω({θ})𝓗` is the unique maximal subspace with the properties (a)--(c)."
The acute restriction is attached to the third clause only.  Accordingly:

* the commutation clause (`proposition3_5_commutations`) and the eigenvector-angle clause
  (`proposition3_5_eigenvector_angle`) are stated at the standing Section 3 scope, for the
  completed direct rotation selected by a crossed-defect isometry — the paper's matched-crossing
  condition (3.5).  Neither requires acuteness, and the eigenvector clause genuinely covers the
  right-angle eigenspace `θ = π/2`;
* the maximal-eigenspace clause (`proposition3_5_angleEigenspace_uniqueMaximal`) keeps the acute
  hypothesis, because the source puts it there.

`proposition3_5_commutations_acute` and `proposition3_5_eigenvector_angle_acute` read the same
two clauses on the canonical acute direct rotation, for consumers that hold `IsAcute` rather
than a crossed-defect isometry.

The implementation in `DavisKahan.Geometry.Angle.Proposition35Infinite`
constructs the literal bounded angle

`Theta = arcsin |P - Q|`,

the acute direct rotation `W`, and the quarter turn `J` from the polar resolution

`W = cos Theta + J sin Theta`.

`DavisKahan.Geometry.Angle.Proposition35Exponential` further proves the
arbitrary-dimensional exponential form `W = exp (J Theta)` from that resolution,
using only the supported identity `J^2 Theta = -Theta` rather than a global
`J^2 = -1` assumption.

The theorems below expose that functional-calculus representation together with
the six printed assertions: the four commutations, the vector-angle identity on
an angle eigenvector, and the unique maximality of the corresponding angle
eigenspace under the paper's conditions (a)--(c).
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan1970


open DavisKahan
open DavisKahan.Proposition35

noncomputable section

/-- The literal operator angle used in Proposition 3.5. -/
alias proposition3_5_angleOperator := section3AngleOperator

/-- The paper's direct rotation in Proposition 3.5. -/
alias proposition3_5_directRotation := section3DirectRotation

/-- The paper's quarter turn `J`, zero on the zero-angle space. -/
alias proposition3_5_quarterTurn := section3QuarterTurn

/-! The real functional calculus on `H →L[𝕜] H`, and the two scalar-action facts Mathlib
pairs it with, are theorems at every `RCLike` field
(`ContinuousLinearMap.continuousFunctionalCalculusReal`), so they are activated here rather
than quantified over.  Until 2026-09-04 they were section `variable`s and explicit binders, so
every source-facing theorem in this file asked its caller for three instances that instance
search finds.  They are `local instance 100` rather than global because a global
`Algebra ℝ (E →L[𝕜] E)` makes Lean's `•` elaborator drop an author-written `((r : ℝ) : 𝕜) •`
coercion. -/
attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal

/-- The assembled regular-and-defect quarter-turn candidate for a general pair.
The two summands act on orthogonal blocks. -/
noncomputable def corollary3_2_quarterTurn
    {𝕜 : Type*} [RCLike 𝕜]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [CompleteSpace H]
    (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection]
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    H →L[𝕜] H :=
  section3QuarterTurn U V + crossedDefectQuarterTurn U V J

/-- The spectral eigenspace `Omega({theta}) H` at an angle eigenvalue. -/
alias proposition3_5_angleEigenspace := section3AngleEigenspace

section Generic

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]
variable (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

/-- The paper's quarter turn for a chosen completed nonacute direct rotation.
It is defined by the same polar construction as on the acute branch. -/
noncomputable def corollary3_2_nonacuteQuarterTurn
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    H →L[𝕜] H :=
  section3NonacuteQuarterTurn U V J

/-- Equation (1.18), exponential form of a chosen distinguished direct rotation in arbitrary
Hilbert dimension: `U = exp (J Theta)`.  The crossed-defect isometry selects the completion
when the pair is not acute. -/
theorem equation1_18_directRotation_exponential
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    nonacuteDirectRotation U V J =
      NormedSpace.exp
        (corollary3_2_nonacuteQuarterTurn U V J * proposition3_5_angleOperator U V) := by
  change nonacuteDirectRotation U V J =
    NormedSpace.exp
      (section3NonacuteQuarterTurn U V J * section3AngleOperator U V)
  exact nonacuteDirectRotation_eq_exp_nonacuteQuarterTurn_mul_angleOperator U V J

/-- Equation (1.18), trigonometric form of a chosen distinguished direct rotation. -/
theorem equation1_18_directRotation_resolution
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    nonacuteDirectRotation U V J =
      section3CosAngleOperator U V +
        corollary3_2_nonacuteQuarterTurn U V J ∘L section3SinAngleOperator U V := by
  simpa [corollary3_2_nonacuteQuarterTurn] using
    nonacuteDirectRotation_eq_cos_add_quarterTurn_sin U V J

/-- The defining polar resolution of the quarter turn used by Proposition 3.5:
`W = cos Theta + J sin Theta`. -/
theorem proposition3_5_directRotation_resolution (hacute : TauCeti.IsAcute U V) :
    proposition3_5_directRotation U V =
      section3CosAngleOperator U V +
        proposition3_5_quarterTurn U V ∘L section3SinAngleOperator U V :=
  section3DirectRotation_eq_cos_add_quarterTurn_sin U V hacute

/-- The functional-calculus representation immediately preceding Proposition 3.5:
`U = exp (J Theta)` for the canonical direct rotation of an acute pair. -/
theorem proposition3_5_directRotation_exponential (hacute : TauCeti.IsAcute U V) :
    proposition3_5_directRotation U V =
      NormedSpace.exp
        (proposition3_5_quarterTurn U V * proposition3_5_angleOperator U V) :=
  section3DirectRotation_eq_exp_quarterTurn_mul_angleOperator U V hacute

/-- Interchanging the subspaces leaves the arbitrary-dimensional bounded angle unchanged. -/
theorem corollary3_2_angleOperator_symm :
    proposition3_5_angleOperator V U = proposition3_5_angleOperator U V :=
  section3AngleOperator_symm U V

/-- On the acute branch, the arbitrary-dimensional quarter turn used in the paper's polar
resolution changes sign when the subspaces are interchanged. -/
theorem corollary3_2_quarterTurn_symm :
    proposition3_5_quarterTurn V U = -proposition3_5_quarterTurn U V :=
  section3QuarterTurn_symm U V

/-- The skew part of every completed nonacute direct rotation has modulus
exactly `sin Theta`. -/
theorem corollary3_2_nonacute_skew_modulus
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    (nonacuteDirectRotation U V J - section3CosAngleOperator U V).modulus =
      section3SinAngleOperator U V :=
  modulus_nonacuteDirectRotation_sub_cosine U V J

/-- The full nonacute polar resolution from the paper: `W = cos Theta + J sin Theta`. -/
theorem corollary3_2_nonacute_directRotation_resolution
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    nonacuteDirectRotation U V J =
      section3CosAngleOperator U V +
        corollary3_2_nonacuteQuarterTurn U V J ∘L section3SinAngleOperator U V := by
  simpa [corollary3_2_nonacuteQuarterTurn] using
    nonacuteDirectRotation_eq_cos_add_quarterTurn_sin U V J


/-- Exponential form for a chosen completed direct rotation outside the acute case. -/
theorem corollary3_2_nonacute_directRotation_exponential
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    nonacuteDirectRotation U V J =
      NormedSpace.exp
        (corollary3_2_nonacuteQuarterTurn U V J * proposition3_5_angleOperator U V) :=
  equation1_18_directRotation_exponential U V J

/-- Reversing the ordered pair and the crossed-defect choice negates the paper's
quarter turn. -/
theorem corollary3_2_nonacuteQuarterTurn_symm
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    corollary3_2_nonacuteQuarterTurn V U (swapCrossedDefectEquiv U V J) =
      -corollary3_2_nonacuteQuarterTurn U V J := by
  rw [corollary3_2_nonacuteQuarterTurn, corollary3_2_nonacuteQuarterTurn,
    section3NonacuteQuarterTurn, section3NonacuteQuarterTurn]
  have hW := nonacuteDirectRotation_swap U V J
  have hC := section3CosAngleOperator_symm U V
  have hsum0 := nonacuteDirectRotation_add_star_eq_two_absoluteValue U V J
  have hCeq := section3CosAngleOperator_eq_canonicalAbsoluteValue U V
  have hsum :
      nonacuteDirectRotation U V J + star (nonacuteDirectRotation U V J) =
        section3CosAngleOperator U V + section3CosAngleOperator U V := by
    simpa [hCeq] using hsum0
  have hD :
      nonacuteDirectRotation V U (swapCrossedDefectEquiv U V J) -
          section3CosAngleOperator V U =
        -(nonacuteDirectRotation U V J - section3CosAngleOperator U V) := by
    rw [hW, hC]
    have hsW : star (nonacuteDirectRotation U V J) =
        section3CosAngleOperator U V + section3CosAngleOperator U V -
          nonacuteDirectRotation U V J := by
      apply eq_sub_iff_add_eq.mpr
      simpa only [add_comm] using hsum
    rw [hsW]
    abel
  rw [hD, ContinuousLinearMap.polarPartial_neg]

/-- Full-scope Corollary 3.2 for a chosen direct rotation: the angle is symmetric,
the paper quarter turn changes sign, and the reversed direct rotation is the
adjoint. -/
theorem corollary3_2
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    proposition3_5_angleOperator V U = proposition3_5_angleOperator U V ∧
      corollary3_2_nonacuteQuarterTurn V U (swapCrossedDefectEquiv U V J) =
        -corollary3_2_nonacuteQuarterTurn U V J ∧
      nonacuteDirectRotation V U (swapCrossedDefectEquiv U V J) =
        star (nonacuteDirectRotation U V J) :=
  ⟨section3AngleOperator_symm U V,
    corollary3_2_nonacuteQuarterTurn_symm U V J,
    nonacuteDirectRotation_swap U V J⟩

/-- Reversal symmetry for the general chosen-defect quarter-turn construction.
For any chosen identification of the crossed defects, reversing the ordered
pair uses the inverse identification.  The operator angle is unchanged and the
assembled quarter turn changes sign. -/
theorem corollary3_2_chosenDefect_symmetry
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    proposition3_5_angleOperator V U = proposition3_5_angleOperator U V ∧
      corollary3_2_quarterTurn V U (swapCrossedDefectEquiv U V J) =
        -corollary3_2_quarterTurn U V J := by
  refine ⟨section3AngleOperator_symm U V, ?_⟩
  rw [corollary3_2_quarterTurn, corollary3_2_quarterTurn,
    section3QuarterTurn_symm U V, crossedDefectQuarterTurn_swap U V J]
  abel

/-- The corresponding chosen nonacute direct rotation reverses to its adjoint. -/
theorem corollary3_2_directRotation_swap
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    nonacuteDirectRotation V U (swapCrossedDefectEquiv U V J) =
      star (nonacuteDirectRotation U V J) :=
  nonacuteDirectRotation_swap U V J

/-! ### The first two clauses, at the paper's own scope

Davis and Kahan write Proposition 3.5 as three assertions and restrict **only the third** to
the acute case: "`Θ` commutes with `P`, with `Q`, with `J`, and with `U`.  For every eigenvalue
`θ`, the eigenvectors `x` satisfy `∠(x, Ux) = θ`.  *In the acute case*, for every eigenvalue
`θ`, the eigenspace `Ω({θ})𝓗` is the unique maximal subspace with the properties (a)--(c)."

So the first two clauses live at the standing Section 3 scope, where a crossed-defect isometry
`J` selects a completed direct rotation and the pair need not be acute.  That is the scope the
two theorems below carry: the only hypothesis beyond the ambient Section 3 setting is the
isometry `J` itself, which is the paper's matched-crossing condition (3.5) in Lean form.

The `*_acute` twins below are the same two clauses read on the *canonical acute* direct
rotation `section3DirectRotation` and its quarter turn, rather than on a completed rotation.
They are kept because acute-only consumers hold `IsAcute` rather than a crossed-defect
isometry.  They are not corollaries of the nonacute theorems: this repository does not
currently prove that a completed rotation agrees with the canonical acute one when the pair is
acute, so the two families are about different (if morally identical) operators. -/

/-- **Davis--Kahan 1970, Proposition 3.5, the four commutation assertions**, at the standing
Section 3 scope.

`Θ` commutes with `P`, with `Q`, with the quarter turn `J`, and with the direct rotation `U`.
No acuteness: `J` here is the quarter turn of the completed direct rotation selected by the
crossed-defect isometry, and the commutations for `P` and `Q` never needed acuteness at all. -/
theorem proposition3_5_commutations
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V) :
    Commute (proposition3_5_angleOperator U V) (U.starProjection) ∧
      Commute (proposition3_5_angleOperator U V) (V.starProjection) ∧
      Commute (proposition3_5_angleOperator U V) (corollary3_2_nonacuteQuarterTurn U V J) ∧
      Commute (proposition3_5_angleOperator U V) (nonacuteDirectRotation U V J) :=
  ⟨section3AngleOperator_comm_projection U V,
    section3AngleOperator_comm_projection_right U V,
    section3AngleOperator_comm_nonacuteQuarterTurn U V J,
    section3AngleOperator_comm_nonacuteDirectRotation U V J⟩

/-- The four commutations read on the canonical acute direct rotation and its quarter turn.
Kept for acute-only consumers; see the section note on why this is not a corollary of
`proposition3_5_commutations`. -/
theorem proposition3_5_commutations_acute (hacute : TauCeti.IsAcute U V) :
    Commute (proposition3_5_angleOperator U V) (U.starProjection) ∧
      Commute (proposition3_5_angleOperator U V) (V.starProjection) ∧
      Commute (proposition3_5_angleOperator U V) (proposition3_5_quarterTurn U V) ∧
      Commute (proposition3_5_angleOperator U V) (proposition3_5_directRotation U V) :=
  ⟨section3AngleOperator_comm_projection U V,
    section3AngleOperator_comm_projection_right U V,
    section3AngleOperator_comm_quarterTurn U V hacute,
    section3AngleOperator_comm_directRotation U V hacute⟩

/-- **Davis--Kahan 1970, Proposition 3.5, eigenvector assertion**, at the standing Section 3
scope.

If `x ≠ 0` is an eigenvector of `Theta` with eigenvalue `theta`, the vector angle from `x` to
its direct rotation is exactly `theta`.  `vectorAngle` is the paper's vector angle (1.14),
using the real part of the inner product.

No acuteness.  The direct rotation is the completion selected by the crossed-defect isometry,
so the statement covers the right-angle eigenspace `theta = pi/2` that acuteness exists to
exclude; see `vectorAngle_nonacuteDirectRotation_eq_of_angleOperator_apply` for why that
endpoint needs no separate argument. -/
theorem proposition3_5_eigenvector_angle
    (J : halmosSourceDefect U V ≃ₗᵢ[𝕜] halmosTargetDefect U V)
    {x : H} (hx0 : x ≠ 0) {θ : ℝ}
    (hx : proposition3_5_angleOperator U V x = ((θ : ℝ) : 𝕜) • x) :
    TauCeti.vectorAngle 𝕜 x (nonacuteDirectRotation U V J x) = θ :=
  vectorAngle_nonacuteDirectRotation_eq_of_angleOperator_apply U V J hx0 hx

/-- The eigenvector clause read on the canonical acute direct rotation.  Kept for acute-only
consumers; see the section note on why this is not a corollary of
`proposition3_5_eigenvector_angle`. -/
theorem proposition3_5_eigenvector_angle_acute (hacute : TauCeti.IsAcute U V)
    {x : H} (hx0 : x ≠ 0) {θ : ℝ}
    (hx : proposition3_5_angleOperator U V x = ((θ : ℝ) : 𝕜) • x) :
    TauCeti.vectorAngle 𝕜 x (proposition3_5_directRotation U V x) = θ :=
  vectorAngle_section3DirectRotation_eq_of_angleOperator_apply U V hacute hx0 hx

/-- The actual angle eigenspace is the fixed-cosine Halmos eigenspace used by
the paper's maximality argument. -/
theorem proposition3_5_angleEigenspace_eq_fixedCosineSubspace
    (hacute : TauCeti.IsAcute U V) {θ : ℝ}
    (hθ : Module.End.HasEigenvalue (proposition3_5_angleOperator U V).toLinearMap
      ((θ : ℝ) : 𝕜)) :
    proposition3_5_angleEigenspace U V θ = fixedCosineSubspace U V (Real.cos θ) :=
  section3AngleEigenspace_eq_fixedCosineSubspace U V hacute hθ

/-- **Davis--Kahan 1970, Proposition 3.5, maximal-eigenspace assertion.**
For every genuine angle eigenvalue `theta`, `Omega({theta}) H` itself has the
printed properties (a)--(c), and every subspace having those printed properties
is contained in it.  Thus it is the unique maximal such subspace. -/
theorem proposition3_5_angleEigenspace_uniqueMaximal
    (hacute : TauCeti.IsAcute U V) {θ : ℝ}
    (hθ : Module.End.HasEigenvalue (proposition3_5_angleOperator U V).toLinearMap
      ((θ : ℝ) : 𝕜)) :
    IsPrintedFixedCosineReducingSubspace U V
        (proposition3_5_angleEigenspace U V θ) (Real.cos θ) ∧
      ∀ M : Submodule 𝕜 H,
        IsPrintedFixedCosineReducingSubspace U V M (Real.cos θ) →
          M ≤ proposition3_5_angleEigenspace U V θ := by
  have h := proposition3_5_angleEigenspace_maximal U V hacute hθ
  exact
    ⟨isPrintedFixedCosineReducingSubspace_of_isFixedCosineReducingSubspace
        U V (Real.cos θ) h.1,
      h.2⟩

end Generic

end

end DavisKahan1970
end TauCeti
