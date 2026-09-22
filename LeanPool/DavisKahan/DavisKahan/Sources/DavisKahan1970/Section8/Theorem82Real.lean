/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section8.Theorem82
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.RealAngleIdentification
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.AmbientReal
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.SingularValueTransport
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.Complexification.SubmoduleEquiv
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SymmetricNormingFanDominance

/-! # Theorem82Real -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan 1970, Theorem 8.2, over a real Hilbert space

Standing assumption 1 of the source says the Hilbert space is "real or
complex".  Every Section 8 declaration in this repository was stated over `ℂ`.
This module descends Theorem 8.2 to a real Hilbert space.

## Why this is an exact transport, where Theorem 8.1 was not

`Section8/Theorem81Real.lean` had to do real work: Theorem 8.1 *asserts
the existence* of the canonical branch, so its real form has to exhibit a real
subspace whose complexification is the complex branch, and that needed the
bounded-gap spectral descent `realBoundedSpectralSubspaceIicOfGap`.  Picking an
arbitrary reducing subspace would not have done.

Theorem 8.2 carries no such existential.  Both subspaces are supplied by the
caller together with their spectral placements, and every printed hypothesis
and every conclusion is preserved **and reflected** by complexification:

* `spectrumIn_complexifySubmodule_iff` for the three spectral placements;
* `complexify_reduces_iff` for `P` reducing `A`;
* `norm_complexify` for both smallness alternatives;
* `directedGap_complexifySubmodule` and `subspaceGap_complexifySubmodule` for
  the conclusions.

So the theorems below are exact transports.  They add no hypothesis the printed
statement does not have: no acuteness, no branch selection, no dimension
restriction is introduced by the descent.

## The printed residual

`residual_eq_comp_subtypeL` identifies the residual `R = (A + H)E₀ - E₀A₀` of
equation (1.8) with `H E₀` from invariance of `P` alone, and that argument
never sees the scalars; it is now stated over any `RCLike` field.  With
`norm_comp_subtypeL_eq_norm_comp_starProjection`, also scalar-generic, the
printed residual norm becomes `‖H P_P‖`, which complexifies term by term.  That
is `norm_residual_complexify` below.

## The two `sin 2Θ` estimates Theorem 8.2 inherits, over `ℝ`

Theorem 8.2's printed statement carries the `sin 2Θ` theorem's own conclusions
alongside `Θ < π/4`, so the real surface has to carry them too.  Two further
ingredients do that, and no perturbation theory is re-run for either:

* `complexify_sinTwoAngleOperator` -- the ambient one-sided `sin 2Θ` operator
  `2 P_{Qᗮ} P_P P_Q` is a real scalar times a product of three orthogonal
  projections, each of which complexifies, so the operator-norm estimates
  transport;
* the paper's own unitarily invariant norm scope needs no new transport at all:
  `sinTwoTheta_ambient_bounded_symmetricNorming_real` is already stated over `ℝ`, and the
  only missing piece was the real spectral dictionary
  `spectrum_compressOperatorReal_subset_of_spectrumIn`, the real counterpart of
  `spectrum_compressOperator_subset_of_spectrumIn`.

The residual alternative is also available at every source unitarily invariant
norm.  The sharp factor-two estimate is proved once over `ℂ`; the real endpoint
uses `complexifySubmoduleEquiv` to identify the printed rectangular residual with
its complex counterpart and transports its complete approximation-singular
sequence back without loss.

## Main results

* `theorem8_2_perturbationHalfGap_real`;
* `theorem8_2_residualHalfGap_real`;
* `theorem8_2_branch_directed_real` -- the printed disjunction;
* `theorem8_2_perturbationHalfGap_real_maximalAngle_lt`,
  `theorem8_2_branch_real_maximalAngle_lt` and
  `theorem8_2_branch_real_maximalAngle_lt_of_crossedDefects` -- the
  printed `Θ < π/4`, under the finite form of (1.5) and under Section 3's
  standing assumption (3.5) respectively; the last carries no dimension
  hypothesis of any kind;
* `theorem8_2_sinTwoTheta_perturbation_real` and
  `theorem8_2_sinTwoTheta_residual_real` -- the inherited `sin 2Θ`
  estimates at the operator norm;
* `theorem8_2_sinTwoTheta_perturbation_real_symmetricNorming` and
  `theorem8_2_sinTwoTheta_residual_real_symmetricNorming` -- both inherited
  `sin 2Θ` estimates at every source unitarily invariant norm;
* `theorem8_2_real` -- the whole printed theorem over `ℝ`.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46: standing assumption 1 and
  Theorem 8.2.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan1970
namespace Section8


open DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation
open TauCeti.DavisKahan.Foundation.RealComplexification
open scoped TauCeti.CompleteSubspace

noncomputable section

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-! ### 1. The printed residual complexifies -/

/-- **The printed residual (1.8) has the same norm before and after
complexification.**

Both sides reduce to `‖H P_P‖` by `residual_eq_comp_subtypeL` and
`norm_comp_subtypeL_eq_norm_comp_starProjection`, and the complexified
projection is the complexification of the projection
(`starProjection_complexifySubmodule`), so `norm_complexify` closes it. -/
theorem norm_residual_complexify
    (A K : E →L[ℝ] E) (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    (hPinv : ∀ x ∈ P, A x ∈ P) :
    ‖residual (complexify A + complexify K) (complexifySubmodule P).subtypeL
        (compressOperator (complexifySubmodule P) (complexify A))‖ =
      ‖residual (A + K) P.subtypeL (compressOperator P A)‖ := by
  classical
  have : CompleteSpace P :=
    (P.isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  have : CompleteSpace (complexifySubmodule P) :=
    ((complexifySubmodule P).isComplete_coe_of_hasOrthogonalProjection).completeSpace_coe
  have hPinvC : ∀ z ∈ complexifySubmodule P, complexify A z ∈ complexifySubmodule P :=
    fun _ hz => mapsTo_complexifySubmodule hPinv hz
  rw [BoundedOperator.residual_eq_comp_subtypeL (complexify A) (complexify K)
      (complexifySubmodule P) hPinvC,
    BoundedOperator.residual_eq_comp_subtypeL A K P hPinv,
    TauCeti.norm_comp_subtypeL_eq_norm_comp_starProjection,
    TauCeti.norm_comp_subtypeL_eq_norm_comp_starProjection,
    starProjection_complexifySubmodule, ← complexify_comp, norm_complexify]

omit [CompleteSpace E] in
/-- **The printed residual complexifies exactly through the canonical trial-space
coordinate equivalence.**

The complex Theorem 8.2 residual acts on `complexifySubmodule P`, whereas the
literal complexification of the real residual acts on `RealComplexification P`.
`complexifySubmoduleEquiv P` identifies those domains, and after that coordinate
change the two residuals are equal as bounded operators. -/
theorem residual_complexify_equiv
    (A K : E →L[ℝ] E) (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    (hPinv : ∀ x ∈ P, A x ∈ P) :
    (residual (complexify A + complexify K) (complexifySubmodule P).subtypeL
        (compressOperator (complexifySubmodule P) (complexify A))) ∘L
          (complexifySubmoduleEquiv P).toContinuousLinearEquiv.toContinuousLinearMap =
      complexify (residual (A + K) P.subtypeL (compressOperator P A)) := by
  have hPinvC : ∀ z ∈ complexifySubmodule P,
      complexify A z ∈ complexifySubmodule P :=
    fun _ hz => mapsTo_complexifySubmodule hPinv hz
  rw [BoundedOperator.residual_eq_comp_subtypeL (complexify A) (complexify K)
      (complexifySubmodule P) hPinvC,
    BoundedOperator.residual_eq_comp_subtypeL A K P hPinv]
  apply ContinuousLinearMap.ext
  intro w
  change (complexify K)
      (((complexifySubmoduleEquiv P w : complexifySubmodule P) :
        RealComplexification E)) =
    complexify (K ∘L P.subtypeL) w
  rw [coe_complexifySubmoduleEquiv_eq_complexify_subtypeL,
    RealComplexification.complexify_comp]
  rfl

omit [CompleteSpace E] in
/-- **The complex and real Theorem 8.2 residuals have the same complete
approximation-singular sequence.**

The only mismatch is the canonical isometric coordinate change between the
complexification of the real trial space and the complexified trial subspace.
This is the rectangular transport needed by every source unitarily invariant
norm; unlike `norm_residual_complexify`, it preserves the entire singular data,
not merely the operator norm. -/
theorem sameApproximationSingularSequence_residual_complexify
    (A K : E →L[ℝ] E) (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    (hPinv : ∀ x ∈ P, A x ∈ P) :
    ExactSinTheta.SameApproximationSingularSequence
      (complexify (residual (A + K) P.subtypeL (compressOperator P A)))
      (residual (complexify A + complexify K) (complexifySubmodule P).subtypeL
        (compressOperator (complexifySubmodule P) (complexify A))) := by
  let U := LinearIsometryEquiv.refl Complex (RealComplexification E)
  let W := complexifySubmoduleEquiv P
  have hcoord :
      U.toContinuousLinearEquiv.toContinuousLinearMap ∘L
          complexify (residual (A + K) P.subtypeL (compressOperator P A)) ∘L
          W.symm.toContinuousLinearEquiv.toContinuousLinearMap =
        residual (complexify A + complexify K) (complexifySubmodule P).subtypeL
          (compressOperator (complexifySubmodule P) (complexify A)) := by
    apply ContinuousLinearMap.ext
    intro z
    let w := W.symm z
    have hw : W w = z := W.apply_symm_apply z
    have h := congrArg (fun L => L w) (residual_complexify_equiv A K P hPinv)
    simpa [U, W, w, hw] using h.symm
  exact ExactSinTheta.SameApproximationSingularValues.of_isometricEquiv_comp
    U W hcoord

/-! ### 1b. The three hypothesis transports, once

Every theorem below complexifies the same configuration, so the three
hypothesis transports are named here instead of being repeated in each proof.
They are `private`: each is a one-line composition of an existing preservation
lemma with a rewrite, and none is a statement about Theorem 8.2. -/

/-- Self-adjointness in the `IsSelfAdjointOperator` spelling survives
complexification. -/
private theorem complexify_isSelfAdjointOperator {T : E →L[ℝ] E}
    (hT : T.IsSymmetric) : (complexify T).IsSymmetric :=
  ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    ((complexify_isSelfAdjoint_iff T).2
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hT))

omit [CompleteSpace E] in
/-- A spectral placement for the perturbed operator on a real subspace becomes
the same placement for the complexified pair on the complexified subspace. -/
private theorem spectrumIn_complexify_add {A K : E →L[ℝ] E} {U : Submodule ℝ E}
     {s : Set ℝ}
    (h : Foundation.SpectrumIn (A + K) U s) :
    Foundation.SpectrumIn (complexify A + complexify K) (complexifySubmodule U) s := by
  rw [show complexify A + complexify K = complexify (A + K) from
    (complexify_add A K).symm]
  exact spectrumIn_complexifySubmodule U (A + K) _ h

omit [CompleteSpace E] in
/-- The same transport on the orthogonal complement, where complexification and
orthogonal complementation have to be exchanged. -/
private theorem spectrumIn_orthogonal_complexify_add {A K : E →L[ℝ] E}
    {U : Submodule ℝ E} {s : Set ℝ}
    (h : Foundation.SpectrumIn (A + K) Uᗮ s) :
    Foundation.SpectrumIn (complexify A + complexify K) (complexifySubmodule U)ᗮ s := by
  rw [show complexify A + complexify K = complexify (A + K) from
      (complexify_add A K).symm,
    ← complexifySubmodule_orthogonal U]
  exact spectrumIn_complexifySubmodule Uᗮ (A + K) _ h

/-! ### 2. The two printed alternatives over `ℝ` -/

/-- **Davis--Kahan 1970, Theorem 8.2, perturbation alternative, over a REAL
Hilbert space.**

`‖H‖ < δ/2` together with the printed spectral placement of `A₀` gives the
directed quarter-angle bound `directedGap P Q < √2/2`, exactly as over `ℂ`.
Every hypothesis is the real reading of the printed one, and the proof is the
complexification transport described in this module's header; the perturbation
theory itself is not re-run. -/
theorem theorem8_2_perturbationHalfGap_real
    {A K : E →L[ℝ] E} (hA : A.IsSymmetric) (hK : K.IsSymmetric)
    {P Q : Submodule ℝ E} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : A.Reduces P)
    (hP : Foundation.SpectrumIn A P (Set.Icc (beta - delta / 2) (alpha + delta / 2)))
    (hsmall : ‖K‖ < delta / 2) :
    P.directedProjectionGap Q < Real.sqrt 2 / 2 := by
  have hsmallc : ‖complexify K‖ < delta / 2 := by
    rw [norm_complexify]; exact hsmall
  have hmain := theorem8_2_perturbationHalfGap_complex
    (complexify_isSelfAdjointOperator hA) (complexify_isSelfAdjointOperator hK)
    hdelta hab (spectrumIn_complexify_add hQ)
    (spectrumIn_orthogonal_complexify_add hQperp)
    ((complexify_reduces_iff A P).2 hPred)
    (spectrumIn_complexifySubmodule P A _ hP) hsmallc
  rwa [directedGap_complexifySubmodule] at hmain

/-- **Davis--Kahan 1970, Theorem 8.2, residual alternative, over a REAL Hilbert
space.**

`‖R‖ < δ/2` for the printed residual (1.8) of equation (1.8), with the same
directed conclusion.  Krein's completion is not re-proved over `ℝ`: the residual
norm is transported by `norm_residual_complexify` and the complex alternative is
applied. -/
theorem theorem8_2_residualHalfGap_real
    {A K : E →L[ℝ] E} (hA : A.IsSymmetric) (hK : K.IsSymmetric)
    {P Q : Submodule ℝ E} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : A.Reduces P)
    (hP : Foundation.SpectrumIn A P (Set.Icc (beta - delta / 2) (alpha + delta / 2)))
    (hRsmall : ‖residual (A + K) P.subtypeL (compressOperator P A)‖ < delta / 2) :
    P.directedProjectionGap Q < Real.sqrt 2 / 2 := by
  have hRsmallc : ‖residual (complexify A + complexify K)
      (complexifySubmodule P).subtypeL
      (compressOperator (complexifySubmodule P) (complexify A))‖ < delta / 2 := by
    rw [norm_residual_complexify A K P hPred.1]
    exact hRsmall
  have hmain := theorem8_2_residualHalfGap_complex
    (complexify_isSelfAdjointOperator hA) (complexify_isSelfAdjointOperator hK)
    hdelta hab (spectrumIn_complexify_add hQ)
    (spectrumIn_orthogonal_complexify_add hQperp)
    ((complexify_reduces_iff A P).2 hPred)
    (spectrumIn_complexifySubmodule P A _ hP) hRsmallc
  rwa [directedGap_complexifySubmodule] at hmain

/-- **Theorem 8.2's printed disjunction over a REAL Hilbert space.**  Either
printed smallness alternative gives the directed quarter-angle bound. -/
theorem theorem8_2_branch_directed_real
    {A K : E →L[ℝ] E} (hA : A.IsSymmetric) (hK : K.IsSymmetric)
    {P Q : Submodule ℝ E} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : A.Reduces P)
    (hP : Foundation.SpectrumIn A P (Set.Icc (beta - delta / 2) (alpha + delta / 2)))
    (halt : ‖K‖ < delta / 2 ∨
      ‖residual (A + K) P.subtypeL (compressOperator P A)‖ < delta / 2) :
    P.directedProjectionGap Q < Real.sqrt 2 / 2 := by
  rcases halt with hsmall | hRsmall
  · exact theorem8_2_perturbationHalfGap_real hA hK hdelta hab hQ hQperp
      hPred hP hsmall
  · exact theorem8_2_residualHalfGap_real hA hK hdelta hab hQ hQperp
      hPred hP hRsmall

/-! ### 3. The printed `Θ < π/4` over `ℝ`

Neither of the two bridges from the directed bound to the printed symmetric
conclusion needs the complexification at all: both
`subspaceGap_eq_directedGap_of_finrank_eq` -- equation (1.5) in its finite form
-- and `subspaceGap_eq_directedGap_of_crossedDefects` -- Section 3's standing
assumption (3.5) -- are `RCLike`-generic, as is
`maximalAngle_lt_pi_div_four_iff`.  So the real forms below read the printed
`Θ < π/4` off the real directed theorems above with no further transport, and
the dimension-free one carries no dimension hypothesis of any kind. -/

/-- **Davis--Kahan 1970, Theorem 8.2, printed conclusion `Θ < π/4` over a REAL
Hilbert space, under the finite form of the standing convention (1.5).**

The real counterpart of `theorem8_2_perturbationHalfGap_maximalAngle_lt`.
Finite dimensionality and equal rank are the printed statement's own standing
convention, exactly as over `ℂ`. -/
theorem theorem8_2_perturbationHalfGap_real_maximalAngle_lt
    [FiniteDimensional ℝ E]
    {A K : E →L[ℝ] E} (hA : A.IsSymmetric) (hK : K.IsSymmetric)
    {P Q : Submodule ℝ E} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : A.Reduces P)
    (hP : Foundation.SpectrumIn A P (Set.Icc (beta - delta / 2) (alpha + delta / 2)))
    (hrank : Module.finrank ℝ P = Module.finrank ℝ Q)
    (hsmall : ‖K‖ < delta / 2) :
    maximalAngle P Q < Real.pi / 4 := by
  have hdir := theorem8_2_perturbationHalfGap_real hA hK hdelta hab hQ
    hQperp hPred hP hsmall
  have hlt : P.projectionGap Q < Real.sqrt 2 / 2 := by
    rw [subspaceGap_eq_directedGap_of_finrank_eq P Q hrank]
    exact hdir
  exact (DavisKahan1970.Section8.maximalAngle_lt_pi_div_four_iff P Q).2 hlt

/-- **Davis--Kahan 1970, Theorem 8.2, printed conclusion `Θ < π/4` over a REAL
Hilbert space, in any dimension, under Section 3's standing assumption (3.5).**

The real counterpart of `maximalAngle_lt_pi_div_four_of_crossedDefects`, applied
to Theorem 8.2's printed disjunction: either printed smallness alternative, plus
(3.5) in its constructive form, gives the printed symmetric conclusion with
**no** finite-dimensionality and **no** rank hypothesis, over `ℝ` exactly as
over `ℂ`. -/
theorem theorem8_2_branch_real_maximalAngle_lt_of_crossedDefects
    {A K : E →L[ℝ] E} (hA : A.IsSymmetric) (hK : K.IsSymmetric)
    {P Q : Submodule ℝ E} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : A.Reduces P)
    (hP : Foundation.SpectrumIn A P (Set.Icc (beta - delta / 2) (alpha + delta / 2)))
    (hcross : CrossedDefectsEquivalent P Q)
    (halt : ‖K‖ < delta / 2 ∨
      ‖residual (A + K) P.subtypeL (compressOperator P A)‖ < delta / 2) :
    maximalAngle P Q < Real.pi / 4 :=
  maximalAngle_lt_pi_div_four_of_crossedDefects hcross
    (theorem8_2_branch_directed_real hA hK hdelta hab hQ hQperp hPred hP halt)

/-- **Theorem 8.2's printed disjunction, printed conclusion `Θ < π/4`, over a
REAL Hilbert space, under the finite form of the standing convention (1.5).**

The real counterpart of `theorem8_2_branch_maximalAngle_lt`, and the form
`theorem8_2_real` packages. -/
theorem theorem8_2_branch_real_maximalAngle_lt [FiniteDimensional ℝ E]
    {A K : E →L[ℝ] E} (hA : A.IsSymmetric) (hK : K.IsSymmetric)
    {P Q : Submodule ℝ E} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : A.Reduces P)
    (hP : Foundation.SpectrumIn A P (Set.Icc (beta - delta / 2) (alpha + delta / 2)))
    (hrank : Module.finrank ℝ P = Module.finrank ℝ Q)
    (halt : ‖K‖ < delta / 2 ∨
      ‖residual (A + K) P.subtypeL (compressOperator P A)‖ < delta / 2) :
    maximalAngle P Q < Real.pi / 4 :=
  maximalAngle_lt_pi_div_four_of_directedGap_lt hrank
    (theorem8_2_branch_directed_real hA hK hdelta hab hQ hQperp hPred hP halt)

/-! ### 4. The `sin 2Θ` estimates Theorem 8.2 inherits, over `ℝ`

The printed statement is "in addition to `δ‖sin 2Θ‖ ≤ 2‖H‖` or
`δ‖sin 2Θ₀‖ ≤ 2‖R‖`, we have `Θ < π/4`", so the real surface carries the two
displayed estimates as well as the quarter angle.  They are the real readings of
`theorem8_2_sinTwoTheta_{perturbation,residual}_source`. -/

omit [CompleteSpace E] in
/-- **The ambient one-sided `sin 2Θ` operator complexifies to its complex
counterpart.**

`sinTwoAngleOperator U V` is `2 P_{Uᗮ} P_V P_U`: the real scalar `2` times a
composition of three orthogonal projections.  `complexify` is real-homogeneous
and functorial, and each projection complexifies to the projection onto the
complexified subspace, so the product does.  Written as two `show`s rather than
`simp` because the two `2`s live in different fields and only the last step is a
cast. -/
theorem complexify_sinTwoAngleOperator (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    complexify (DavisKahanExt.sinTwoAngleOperator U V) =
      DavisKahanExt.sinTwoAngleOperator (complexifySubmodule U)
        (complexifySubmodule V) := by
  change complexify ((2 : ℝ) •
    (Uᗮ.starProjection ∘L V.starProjection ∘L U.starProjection)) = _
  change _ = (2 : ℂ) • ((complexifySubmodule U)ᗮ.starProjection ∘L
    (complexifySubmodule V).starProjection ∘L
      (complexifySubmodule U).starProjection)
  rw [complexify_real_smul, complexify_comp, complexify_comp,
    starProjection_complexifySubmodule_orthogonal,
    starProjection_complexifySubmodule, starProjection_complexifySubmodule,
    show ((2 : ℝ) : ℂ) = (2 : ℂ) from by norm_num]

omit [CompleteSpace E] in
/-- The ambient `sin 2Θ` of a real pair has the operator norm of the complex
`sin 2Θ` of the complexified pair. -/
theorem norm_sinTwoAngleOperator_complexifySubmodule (U V : Submodule ℝ E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖DavisKahanExt.sinTwoAngleOperator (complexifySubmodule U)
        (complexifySubmodule V)‖ =
      ‖DavisKahanExt.sinTwoAngleOperator U V‖ := by
  rw [← complexify_sinTwoAngleOperator U V, norm_complexify]

/-- **The `sin 2Θ` estimate at Theorem 8.2's hypotheses, perturbation form, over
a REAL Hilbert space**: `δ ‖sin 2Θ‖ ≤ 2 ‖H‖`.

The real reading of `theorem8_2_sinTwoTheta_perturbation_complex`.  Nothing is
re-proved: the configuration is complexified, the complex estimate applied, and
both sides read back by `norm_sinTwoAngleOperator_complexifySubmodule` and
`norm_complexify`. -/
theorem theorem8_2_sinTwoTheta_perturbation_real
    {A K : E →L[ℝ] E} (hA : A.IsSymmetric) (hK : K.IsSymmetric)
    {P Q : Submodule ℝ E} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : A.Reduces P) :
    delta * ‖DavisKahanExt.sinTwoAngleOperator Q P‖ ≤ 2 * ‖K‖ := by
  have hmain := theorem8_2_sinTwoTheta_perturbation_complex
    (complexify_isSelfAdjointOperator hA) (complexify_isSelfAdjointOperator hK)
    hdelta hab (spectrumIn_complexify_add hQ)
    (spectrumIn_orthogonal_complexify_add hQperp)
    ((complexify_reduces_iff A P).2 hPred)
  rwa [norm_sinTwoAngleOperator_complexifySubmodule, norm_complexify] at hmain

/-- **The `sin 2Θ` estimate at Theorem 8.2's hypotheses, residual form, over a
REAL Hilbert space**: `δ ‖sin 2Θ‖ ≤ 2 ‖R‖` with `R` the printed residual (1.8).

The real reading of `theorem8_2_sinTwoTheta_residual_complex`, transported the
same way, with the residual norm carried by `norm_residual_complexify`.

As over `ℂ`, the conclusion names the **ambient** `sin 2Θ` of the pair, not the
directed `sin 2Θ₀` of the printed residual inequality; at the operator norm that
is the stronger reading. -/
theorem theorem8_2_sinTwoTheta_residual_real
    {A K : E →L[ℝ] E} (hA : A.IsSymmetric) (hK : K.IsSymmetric)
    {P Q : Submodule ℝ E} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : A.Reduces P) :
    delta * ‖DavisKahanExt.sinTwoAngleOperator Q P‖ ≤
      2 * ‖residual (A + K) P.subtypeL (compressOperator P A)‖ := by
  have hmain := theorem8_2_sinTwoTheta_residual_complex
    (complexify_isSelfAdjointOperator hA) (complexify_isSelfAdjointOperator hK)
    hdelta hab (spectrumIn_complexify_add hQ)
    (spectrumIn_orthogonal_complexify_add hQperp)
    ((complexify_reduces_iff A P).2 hPred)
  rwa [norm_sinTwoAngleOperator_complexifySubmodule,
    norm_residual_complexify A K P hPred.1] at hmain

/-! ### 5. The same estimate at every source unitarily invariant norm, over `ℝ`

`sinTwoTheta_ambient_bounded_symmetricNorming_real` is equation (7.5) over a real Hilbert
space, for every norm in the paper's own class.  Reading it at Theorem 8.2's
configuration needs exactly one thing the complex descent also needed: the
dictionary between `Foundation.SpectrumIn` and `spectrum ℝ` of the compression.
-/

omit [CompleteSpace E] in
/-- **The spectral dictionary between Section 8 and the `sin 2Θ` development,
over `ℝ`.**

The real counterpart of `spectrum_compressOperator_subset_of_spectrumIn`.  It is
**not** obtained by generalizing that theorem's scalars: over a general `RCLike`
field the statement does not even elaborate, because `spectrum ℝ` of an operator
needs an `Algebra ℝ` structure on the `𝕜`-operator algebra and there is none.
The complex proof crosses that gap with `realSpectrum T = spectrum ℝ T`; over
`ℝ` the same crossing is a coercion identity.  `compressOperatorReal U T` is by
definition the `compressOperator U T` of the scalar-generic compression, hence
the honest restriction on an invariant subspace. -/
theorem spectrum_compressOperatorReal_subset_of_spectrumIn
    {T : E →L[ℝ] E} {U : Submodule ℝ E} [U.HasOrthogonalProjection]
    {s : Set ℝ} (h : Foundation.SpectrumIn T U s) :
    spectrum ℝ (DavisKahan1970.compressOperatorReal U T) ⊆ s := by
  intro r hr
  refine h.subset ⟨h.invariant, ?_⟩
  rw [show DavisKahan1970.compressOperatorReal U T = T.restrict h.invariant from
    compressOperator_eq_restrict_of_invariant T U h.invariant] at hr
  simpa using hr

/-- **The `sin 2Θ` estimate at Theorem 8.2's hypotheses, perturbation form, over
a REAL Hilbert space, for every source unitarily invariant norm.**

`δ N(sin 2Θ) ≤ 2 N(H)`, at the paper's own class of unitarily invariant norms
and at Theorem 8.2's own hypotheses.
`theorem8_2_sinTwoTheta_perturbation_real` is the operator-norm reading of
the same inheritance, and `theorem8_2_sinTwoTheta_perturbation_symmetricNorming`
is the complex one.

Nothing is re-proved.  This is equation (7.5) over a real Hilbert space,
`DavisKahan1970.sinTwoTheta_ambient_bounded_symmetricNorming_real`, read with `A + K`
carrying the printed gap on `Q` and with `A` — which `P` reduces by hypothesis —
as the comparison operator, so that the displacement is `-K`.

The conclusion names the paper's literal `sin 2Θ`, the real positive operator
`sinTwoAngleOperatorR Q P`, rather than the modulus-free
`sinTwoAngleOperator` of the operator-norm statement: only the former carries the
whole singular-value list that a general unitarily invariant norm reads. -/
theorem theorem8_2_sinTwoTheta_perturbation_real_symmetricNorming
    (N : ExactSinTheta.SymmetricNormingFunction)
    {A K : E →L[ℝ] E} (hA : A.IsSymmetric) (hK : K.IsSymmetric)
    {P Q : Submodule ℝ E} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : A.Reduces P)
    (hKmem : N.Mem K) :
    N.Mem (sinTwoAngleOperatorR Q P) ∧
      delta * N.gauge (sinTwoAngleOperatorR Q P) ≤ 2 * N.gauge K := by
  have hAsa : IsSelfAdjoint A :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA
  have hKsa : IsSelfAdjoint K :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hK
  have hAKsa : IsSelfAdjoint (A + K) := hAsa.add hKsa
  have hQred : (A + K).Reduces Q := ⟨hQ.invariant, hQperp.invariant⟩
  have hUspec : spectrum ℝ (DavisKahan1970.compressOperatorReal Q (A + K)) ⊆
      Set.Icc beta alpha :=
    spectrum_compressOperatorReal_subset_of_spectrumIn hQ
  have hUspec' : ∀ x ∈ spectrum ℝ (DavisKahan1970.compressOperatorReal Qᗮ (A + K)),
      x ≤ beta - delta ∨ alpha + delta ≤ x :=
    fun _ hx => spectrum_compressOperatorReal_subset_of_spectrumIn hQperp hx
  have hneg : A - (A + K) = (-1 : ℝ) • K := by
    rw [neg_one_smul]
    abel
  have hone : ‖(-1 : ℝ)‖ = 1 := by norm_num
  have hMemNeg : N.Mem (A - (A + K)) := by
    rw [hneg]
    intro htop
    rw [N.extendedGauge_smul, hone] at htop
    rcases ENNReal.mul_eq_top.mp htop with ⟨_, h⟩ | ⟨h, _⟩
    · exact hKmem h
    · exact absurd h (by simp)
  have hgaugeNeg : N.gauge (A - (A + K)) = N.gauge K := by
    rw [hneg, N.gauge_smul _ hKmem, hone, one_mul]
  obtain ⟨hmem, hle⟩ := DavisKahan1970.sinTwoTheta_ambient_bounded_symmetricNorming_real N
    hAKsa hAsa hQred hPred hdelta hab hUspec hUspec' hMemNeg
  exact ⟨hmem, by rwa [hgaugeNeg] at hle⟩

/-- **The `sin 2Θ₀` estimate at Theorem 8.2's hypotheses, residual form, over
a REAL Hilbert space, for every source unitarily invariant norm.**

This is the real counterpart of
`theorem8_2_sinTwoTheta_residual_symmetricNorming`, in the same block form:

`δ N(sin 2Θ₀) ≤ 2 N(R)` read on `sinTwoThetaIdealBlock Q P`.
`theorem8_2_sinTwoTheta_residual_directedAngle_real_symmetricNorming` is the
source-facing statement, on the paper's own trial-side directed angle.

The analytic estimate is not reproved over `ℝ`.  Complexification carries the
directed doubled-angle block exactly, while `residual_complexify_equiv` carries
the printed rectangular residual through the canonical trial-space isometry.
Those identities preserve the complete approximation-singular sequences, so
`SymmetricNormingFunction.mem_complexify_iff`, `gauge_complexify`, and the
heterogeneous singular-sequence transport return both membership and the norm
inequality to the real spaces with no loss in the constant. -/
theorem theorem8_2_sinTwoTheta_residual_real_symmetricNorming
    (N : ExactSinTheta.SymmetricNormingFunction)
    {A K : E →L[ℝ] E} (hA : A.IsSymmetric) (hK : K.IsSymmetric)
    {P Q : Submodule ℝ E} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : A.Reduces P)
    (hRmem : N.Mem (residual (A + K) P.subtypeL (compressOperator P A))) :
    N.Mem (TauCeti.DavisKahan.sinTwoThetaIdealBlock Q P) ∧
      delta * N.gauge (TauCeti.DavisKahan.sinTwoThetaIdealBlock Q P) ≤
        2 * N.gauge (residual (A + K) P.subtypeL (compressOperator P A)) := by
  have hseq := sameApproximationSingularSequence_residual_complexify A K P hPred.1
  have htransport := hseq.normingMem_iff_and_gauge_eq N
  have hRmemComplexified :
      N.Mem (complexify (residual (A + K) P.subtypeL (compressOperator P A))) :=
    (ExactSinTheta.SymmetricNormingFunction.mem_complexify_iff N _).2 hRmem
  have hRmemC :
      N.Mem
        (residual (complexify A + complexify K) (complexifySubmodule P).subtypeL
          (compressOperator (complexifySubmodule P) (complexify A))) :=
    htransport.1.mp hRmemComplexified
  obtain ⟨hBlockMemC, hboundC⟩ :=
    theorem8_2_sinTwoTheta_residual_symmetricNorming N
      (complexify_isSelfAdjointOperator hA) (complexify_isSelfAdjointOperator hK)
      hdelta hab (spectrumIn_complexify_add hQ)
      (spectrumIn_orthogonal_complexify_add hQperp)
      ((complexify_reduces_iff A P).2 hPred) hRmemC
  have hBlockEq :=
    TauCeti.DavisKahan.complexify_sinTwoThetaIdealBlock Q P
  rw [← hBlockEq] at hBlockMemC hboundC
  have hBlockMem :
      N.Mem (TauCeti.DavisKahan.sinTwoThetaIdealBlock Q P) :=
    (ExactSinTheta.SymmetricNormingFunction.mem_complexify_iff N _).1 hBlockMemC
  refine ⟨hBlockMem, ?_⟩
  have hResidualGauge :
      N.gauge
          (residual (complexify A + complexify K) (complexifySubmodule P).subtypeL
            (compressOperator (complexifySubmodule P) (complexify A))) =
        N.gauge (residual (A + K) P.subtypeL (compressOperator P A)) := by
    calc
      N.gauge
          (residual (complexify A + complexify K) (complexifySubmodule P).subtypeL
            (compressOperator (complexifySubmodule P) (complexify A))) =
          N.gauge
            (complexify (residual (A + K) P.subtypeL (compressOperator P A))) :=
        htransport.2.symm
      _ = N.gauge (residual (A + K) P.subtypeL (compressOperator P A)) :=
        ExactSinTheta.SymmetricNormingFunction.gauge_complexify N _
  rw [ExactSinTheta.SymmetricNormingFunction.gauge_complexify, hResidualGauge] at hboundC
  exact hboundC

/-- **Theorem 8.2's printed residual alternative over `ℝ`, on the paper's own
directed angle.**

The real sibling of
`theorem8_2_sinTwoTheta_residual_directedAngle_symmetricNorming`: same residual,
same factor two, and the same trial-side ordering
`Angle.directedSinTwoAngleOperator P Q`, with `P` the trial subspace and `Q` the
subspace whose blocks the gap separates. -/
theorem theorem8_2_sinTwoTheta_residual_directedAngle_real_symmetricNorming
    (N : ExactSinTheta.SymmetricNormingFunction)
    {A K : E →L[ℝ] E} (hA : A.IsSymmetric) (hK : K.IsSymmetric)
    {P Q : Submodule ℝ E} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : A.Reduces P)
    (hRmem : N.Mem (residual (A + K) P.subtypeL (compressOperator P A))) :
    N.Mem (Angle.directedSinTwoAngleOperator P Q) ∧
      delta * N.gauge (Angle.directedSinTwoAngleOperator P Q) ≤
        2 * N.gauge (residual (A + K) P.subtypeL (compressOperator P A)) := by
  obtain ⟨hmem, hle⟩ :=
    theorem8_2_sinTwoTheta_residual_real_symmetricNorming N hA hK hdelta hab hQ hQperp hPred hRmem
  refine ⟨(Angle.mem_directedSinTwoAngleOperator_trialSide_iff _ _ N).mpr hmem, ?_⟩
  rwa [Angle.gauge_directedSinTwoAngleOperator_trialSide]

/-! ### 6. The whole printed theorem over `ℝ` -/

/-- **Davis--Kahan 1970, Theorem 8.2, over a REAL Hilbert space.**

> Add to the hypotheses of the `sin 2θ` theorem either `‖H‖₁ < δ/2` or
> `‖R‖₁ < δ/2`, and assume the spectrum of `A₀` lies in
> `[β - δ/2, α + δ/2]`.  Then, in addition to `δ‖sin 2Θ‖ ≤ 2‖H‖` or
> `δ‖sin 2Θ₀‖ ≤ 2‖R‖`, we have `Θ < π/4`.

The real reading of `theorem8_2_complex`, hypothesis for hypothesis and
conclusion for conclusion: standing assumption 1 of the source admits a real or
complex Hilbert space, and Theorem 8.2 supplies both subspaces as data, so the
descent introduces no hypothesis of its own.

`‖·‖₁` is the bound norm throughout Theorem 8.2, which is what the operator
norms here are; `theorem8_2_sinTwoTheta_perturbation_real_symmetricNorming`
carries the perturbation estimate at the printed norm scope. -/
theorem theorem8_2_real [FiniteDimensional ℝ E]
    {A K : E →L[ℝ] E} (hA : A.IsSymmetric) (hK : K.IsSymmetric)
    {P Q : Submodule ℝ E} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : A.Reduces P)
    (hP : Foundation.SpectrumIn A P (Set.Icc (beta - delta / 2) (alpha + delta / 2)))
    (hrank : Module.finrank ℝ P = Module.finrank ℝ Q)
    (hsmall : ‖K‖ < delta / 2 ∨
      ‖residual (A + K) P.subtypeL (compressOperator P A)‖ < delta / 2) :
    delta * ‖DavisKahanExt.sinTwoAngleOperator Q P‖ ≤ 2 * ‖K‖ ∧
      delta * ‖DavisKahanExt.sinTwoAngleOperator Q P‖ ≤
        2 * ‖residual (A + K) P.subtypeL (compressOperator P A)‖ ∧
      maximalAngle P Q < Real.pi / 4 :=
  ⟨theorem8_2_sinTwoTheta_perturbation_real hA hK hdelta hab hQ hQperp hPred,
    theorem8_2_sinTwoTheta_residual_real hA hK hdelta hab hQ hQperp hPred,
    theorem8_2_branch_real_maximalAngle_lt hA hK hdelta hab hQ hQperp hPred
      hP hrank hsmall⟩

/-! ### Source-exact façades over `ℝ` -/

/-- **Theorem 8.2's retained perturbation bound at the printed source scope over
`ℝ`.** -/
theorem theorem8_2_sinTwoTheta_perturbation_real_sourceExact
    (N : ExactSinTheta.NormalizedUnitaryInvariantNorm.{0, _} ℝ)
    {A K : E →L[ℝ] E} (hA : A.IsSymmetric) (hK : K.IsSymmetric)
    {P Q : Submodule ℝ E} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : A.Reduces P)
    (hKmem : N.Mem K) :
    N.Mem (sinTwoAngleOperatorR Q P) ∧
      delta * N.gauge (sinTwoAngleOperatorR Q P) ≤ 2 * N.gauge K :=
  TauCeti.DavisKahan1970.normalizedUnitaryInvariant_of_symmetricNorming_mul N hdelta two_pos
    hKmem fun M hM =>
      theorem8_2_sinTwoTheta_perturbation_real_symmetricNorming M hA hK hdelta hab hQ
        hQperp hPred hM

/-- **Theorem 8.2's retained residual bound on the directed angle, at the printed
source scope over `ℝ`.** -/
theorem theorem8_2_sinTwoTheta_residual_directedAngle_real_sourceExact
    (N : ExactSinTheta.NormalizedUnitaryInvariantNorm.{0, _} ℝ)
    {A K : E →L[ℝ] E} (hA : A.IsSymmetric) (hK : K.IsSymmetric)
    {P Q : Submodule ℝ E} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : A.Reduces P)
    (hRmem : N.Mem (residual (A + K) P.subtypeL (compressOperator P A))) :
    N.Mem (Angle.directedSinTwoAngleOperator P Q) ∧
      delta * N.gauge (Angle.directedSinTwoAngleOperator P Q) ≤
        2 * N.gauge (residual (A + K) P.subtypeL (compressOperator P A)) :=
  TauCeti.DavisKahan1970.normalizedUnitaryInvariant_of_symmetricNorming_mul N hdelta two_pos
    hRmem fun M hM =>
      theorem8_2_sinTwoTheta_residual_directedAngle_real_symmetricNorming M hA hK hdelta
        hab hQ hQperp hPred hM

end

end Section8
end DavisKahan1970
end TauCeti
