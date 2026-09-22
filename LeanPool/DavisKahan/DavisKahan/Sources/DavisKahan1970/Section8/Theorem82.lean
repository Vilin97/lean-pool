/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section8.Theorem82Branch
import LeanPool.DavisKahan.DavisKahan.Geometry.Halmos.CrossedDefectGap
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SinTwoThetaAmbient
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.AngleGeometry
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.DirectedAngleGeneric
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SymmetricNormingFanDominance

/-! # Theorem82 -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan 1970, Theorem 8.2, under the paper's standing convention

`Section8Perturbation.lean` and `Section8Residual.lean` prove the branch
selection from the printed hypotheses alone, and they conclude with the
*directed* quarter-angle bound `directedGap P Q < √2/2`.  That was deliberate:
with only the printed hypotheses of Theorem 8.2 in scope, the symmetric
projector gap can be `1`, so the conclusion read symmetrically is false.  The
counterexample is recorded in `Section8Perturbation.lean` and is a dimension
mismatch -- `P = ⊥`, `Q = ⊤` on a one-dimensional space.

This module supplies the missing standing convention and derives the printed
conclusion exactly.

## What the paper's `Θ` presupposes

`Θ` is not defined for an arbitrary pair of subspaces.  Section 1 builds it from
the entries `C_j` of a unitary `V` satisfying equation (1.4),

```
V P = Q V,      V Pᗮ = Qᗮ V,
```

and immediately notes that (1.4) forces equation (1.5),

```
dim P H = dim Q H,      dim Pᗮ H = dim Qᗮ H
```

("the second equality is a consequence of the first if `dim P H` is finite").
`Θ_j := arccos (C_j C_j⋆)^{1/2}` and `Θ ≃ diag (Θ_0, Θ_1)` are then defined from
those entries, and the paper's own dictionary (Section 1, after (1.17)) reads

```
‖P - Q‖ = ‖sin Θ‖    (all norms),
```

which is `maximalAngle P Q = arcsin (subspaceGap P Q)` here.  So (1.5) is
exactly the standing hypothesis that makes `Θ < π/4` a meaningful assertion, and
it is the minimal one: it is what the paper states, not something stronger
reverse-engineered from the conclusion.

`IsQuarterAcute P Q` is **not** assumed anywhere below.  It is the conclusion.

## Why the finite form of (1.5), and not the cardinal form

In finite dimensions (1.5) is `finrank ℂ P = finrank ℂ Q`; its second half is
automatic.  Under it, `opNorm_projection_sub_eq_opNorm_sinThetaMap` identifies
the symmetric and directed gaps, and the printed conclusion follows from the
directed theorem with nothing else added.

**CORRECTED 2026-08-11.**  This passage used to display a configuration --
`H := E × E`, `Q := E × 0`, `P := span {e₁, e₂, …} × 0` on a separable
infinite-dimensional `E` -- and assert that under the cardinal reading of (1.5)
"the printed conclusion is **false**, and the counterexample satisfies every
printed hypothesis of Theorem 8.2".  That assertion was wrong, and it was wrong
about a *printed hypothesis it did not check*.

(3.5), stated at Proposition 3.2 of the transcription as
`dim(P𝓗 ∩ Qtilde𝓗) = dim(Ptilde𝓗 ∩ Q𝓗)`, is a **standing** hypothesis of the source from
Section 3 onward: the sentence closing that proposition's proof reads "We shall
assume (3.5) as well as (1.5) except where stated otherwise."  Theorem 8.2 does
not state otherwise, so (3.5) is in force there exactly as (1.5) is.  In the
displayed configuration `P𝓗 ∩ Qtilde𝓗 = 0` while `Ptilde𝓗 ∩ Q𝓗 = span {e₀} × 0`, so the
two crossed dimensions are `0` and `1` and (3.5) **fails**.  It is therefore not
a configuration satisfying every printed hypothesis, and it refutes nothing
about the printed conclusion.

It is, in fact, the paper's own (3.5)-failure example.  The Remark following
Proposition 3.2 takes `𝓗 = ℓ²(ℤ)`, `P𝓗` the sequences with `a_n = 0` for
`n < 0`, `Q𝓗` those with `a_n = 0` for `n ≤ 0`, notes that (1.5) holds with the
bilateral shift as a witness for (1.4), and concludes: "`P Qtilde` is the projector
upon the subspace of sequences with `a_n = 0` for `n ≠ 0`, whereas `Ptilde Q = 0`; so
(3.5) fails."  That is the displayed configuration with the two subspaces
interchanged.  It is machine-checked in this repository as
`Section3.directedGap_asymmetric_coordinateHalfSpace`, together with
`coordinateHalfSpace_dimensions_agree` ((1.5) holds) and
`not_crossedDefectsEquivalent_coordinateHalfSpace` ((3.5) fails).

**What the configuration does show, and what it does not.**  It shows that (1.5)
at the cardinal reading does not by itself identify the symmetric gap with the
directed one: equal (infinite) dimension does not make the two directed gaps
agree, whereas in finite dimensions `P ≤ Q` with equal rank forces `P = Q`.
That was always its real content, and it is why the dimension-free statements
below take (3.5) rather than a dimension count.  It does **not** show that the
printed conclusion fails under the cardinal reading, because (3.5) is printed
too.  Nothing here should be read as settling the cardinal reading either way.

**Why the finite form, then, on its own grounds.**  Two, neither of which is a
counterexample.  First, the paper's own Remark after Proposition 3.2: "Since we
are assuming (1.5), (3.5) will hold automatically if either `dim P𝓗` or
`dim Ptilde𝓗` is finite."  The finite form is thus precisely the regime in which the
standing hypothesis (3.5) is free, so a statement carrying it assumes nothing
the source has not already assumed.  Second, it is the checkable form:
`finrank ℂ P = finrank ℂ Q` is a hypothesis a consumer discharges by counting,
where (3.5) in its constructive form `CrossedDefectsEquivalent` asks for an
isometry between the two crossed defects.

The degenerate `P = ⊥`, `Q = ⊤` example recorded in `Section8Perturbation.lean`
is a separate matter: it is excluded by (1.5) itself, at either reading.

## The dimension-free reading, under Section 3's standing assumption (3.5)

The section above is about (1.5) and remains correct: neither reading of (1.5)
identifies the two directed gaps.  Section 3's *other* standing assumption does.
(3.5) asks that the two crossed defects `P ⊓ Qᗮ` and `Pᗮ ⊓ Q` carry the same
data; `subspaceGap_eq_directedGap_of_crossedDefects` and
`maximalAngle_lt_pi_div_four_of_crossedDefects` deliver the printed conclusion
from it with **no** dimension hypothesis of any kind, and
`theorem8_2_branch_maximalAngle_lt_of_crossedDefects` is Theorem 8.2's
printed disjunction read off them.

So the printed `Θ < π/4` is available in this repository under *either* the
finite form of (1.5) or the standing (3.5) -- and the bilateral-shift
configuration discussed above, which fails (3.5), is exactly what the second of
those rules out.

## What is exported

* `subspaceGap_eq_directedGap_of_finrank_eq` -- the bridge, (1.5) in its finite
  form;
* `subspaceGap_eq_directedGap_of_crossedDefects` and
  `maximalAngle_lt_pi_div_four_of_crossedDefects` -- the same bridge and the
  printed `Θ < π/4` under (3.5), in any dimension;
* `theorem8_2_sinTwoTheta_perturbation_complex` and
  `theorem8_2_sinTwoTheta_residual_complex` -- the `sin 2Θ` conclusions Theorem
  8.2 inherits, specialized to its configuration and stated with its
  hypotheses, so the exported Section 8.2 surface carries them rather than
  merely pointing at Section 7, at the operator norm;
* `theorem8_2_sinTwoTheta_perturbation_symmetricNorming` and
  `theorem8_2_sinTwoTheta_residual_symmetricNorming` -- both of those at the
  printed norm scope, every unitarily invariant norm in the paper's own sense,
  the residual one at the printed *directed* `sin 2Θ₀` and with the printed
  factor `2`; `theorem8_2_sinTwoTheta_residual_all_kyFan` is the same
  content at every Ky Fan level.  What is *not* available at that scope is the
  **ambient** `sin 2Θ` reading of the residual alternative; the measurement is
  at the head of section 2b;
* `theorem8_2_perturbationHalfGap_maximalAngle_lt`,
  `theorem8_2_residualHalfGap_maximalAngle_lt`,
  `theorem8_2_branch_maximalAngle_lt` -- the printed `Θ < π/4`;
* `theorem8_2_complex` -- the whole printed theorem, both alternatives and both
  conclusions, in one statement.

The directed theorems keep their names and are *not* superseded: they are the
strongest statement available from the explicit hypotheses alone, and they are
what the dimension-free consumers use.
-/

open scoped InnerProductSpace
open Module (finrank)

namespace TauCeti
namespace DavisKahan1970
namespace Section8


open DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan.Foundation
open TauCeti.ApproximationNumber
open scoped TauCeti.CompleteSubspace

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-! ### 1. Equation (1.5), and what it buys -/

/-- **Davis--Kahan equation (1.5), finite form.**  For subspaces of equal rank
the symmetric projector gap and the directed gap coincide, so `‖sin Θ‖` may be
computed from either.

This is `TauCeti.opNorm_projection_sub_eq_opNorm_sinThetaMap` in the Section 8
vocabulary; both sides are literally the operator norms that
`Submodule.projectionGap` and `Submodule.directedProjectionGap` unfold to.

Stated over an arbitrary `RCLike` field, with its own binders, because the real
Section 8 descent needs it over `ℝ`; the underlying geometry never sees the
scalars. -/
theorem subspaceGap_eq_directedGap_of_finrank_eq {𝕜 : Type*} [RCLike 𝕜]
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    [FiniteDimensional 𝕜 G]
    (P Q : Submodule 𝕜 G) [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hrank : finrank 𝕜 P = finrank 𝕜 Q) :
    P.projectionGap Q = P.directedProjectionGap Q :=
  TauCeti.opNorm_projection_sub_eq_opNorm_sinThetaMap P Q hrank

/-- Under equation (1.5), a directed quarter-angle bound is the printed
`Θ < π/4`.

Stated over an arbitrary `RCLike` field, with its own binders, so that the real
Section 8 descent reads the same conclusion off the real directed bound. -/
theorem maximalAngle_lt_pi_div_four_of_directedGap_lt {𝕜 : Type*} [RCLike 𝕜]
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    [FiniteDimensional 𝕜 G]
    {P Q : Submodule 𝕜 G} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hrank : finrank 𝕜 P = finrank 𝕜 Q)
    (hdir : P.directedProjectionGap Q < Real.sqrt 2 / 2) :
    maximalAngle P Q < Real.pi / 4 := by
  refine (DavisKahan1970.Section8.maximalAngle_lt_pi_div_four_iff P Q).2 ?_
  change P.projectionGap Q < Real.sqrt 2 / 2
  rw [subspaceGap_eq_directedGap_of_finrank_eq P Q hrank]
  exact hdir

/-- **Equation (1.5), under the paper's own standing assumption instead of a
dimension count.**

Same conclusion as `subspaceGap_eq_directedGap_of_finrank_eq`, with
`[FiniteDimensional ℂ H]` and `finrank P = finrank Q` replaced by Section 3's
standing assumption (3.5) in its constructive form: the two crossed defects
`P ⊓ Qᗮ` and `Pᗮ ⊓ Q` are linearly isometric.

This is the source-faithful hypothesis.  (1.5) alone does not suffice, and that
is the paper's own Remark after Proposition 3.2, machine-checked as
`Section3.directedGap_asymmetric_coordinateHalfSpace`: the bilateral-shift pair
satisfies (1.5), fails (3.5), and has directed gaps `1` and `0`. -/
theorem subspaceGap_eq_directedGap_of_crossedDefects {𝕜 : Type*} [RCLike 𝕜]
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (P Q : Submodule 𝕜 G) [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (h : CrossedDefectsEquivalent P Q) :
    P.projectionGap Q = P.directedProjectionGap Q :=
  subspaceGap_eq_directedGap_of_crossedDefectsEquivalent P Q h

/-- **The printed `Θ < π/4` of Theorem 8.2 from the directed bound, in any
dimension.**

The dimension-free counterpart of
`maximalAngle_lt_pi_div_four_of_directedGap_lt`.  The directed quarter-angle
bound is what `Section8Perturbation.lean` and `Section8Residual.lean` actually
deliver from the printed hypotheses; (3.5) is what turns it into the printed
symmetric conclusion, with no finite-dimensionality anywhere. -/
theorem maximalAngle_lt_pi_div_four_of_crossedDefects {𝕜 : Type*} [RCLike 𝕜]
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    {P Q : Submodule 𝕜 G} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (h : CrossedDefectsEquivalent P Q)
    (hdir : P.directedProjectionGap Q < Real.sqrt 2 / 2) :
    maximalAngle P Q < Real.pi / 4 := by
  refine (DavisKahan1970.Section8.maximalAngle_lt_pi_div_four_iff P Q).2 ?_
  change P.projectionGap Q < Real.sqrt 2 / 2
  rw [subspaceGap_eq_directedGap_of_crossedDefects P Q h]
  exact hdir

/-! ### 2. The `sin 2Θ` conclusions Theorem 8.2 inherits

Theorem 8.2 says "in addition to `δ‖sin 2Θ‖ ≤ 2‖H‖` **or**
`δ‖sin 2Θ₀‖ ≤ 2‖R‖`, we have `Θ < π/4`".  The two displayed inequalities are the
`sin 2Θ` theorem's own conclusions, not new content; they are restated here at
Theorem 8.2's hypotheses so that the exported surface carries the whole printed
assertion. -/

/-- **The `sin 2Θ` estimate at Theorem 8.2's hypotheses, perturbation form.**

`δ ‖sin 2Θ‖ ≤ 2 ‖H‖`, inherited from the maintained `sin 2Θ` development
(`sinTwoTheta_perturbation`) with `Q` as the subspace carrying the printed gap.
Nothing here is re-proved; the printed spectral placement of `Λ₀` and `Λ₁` is
exactly a `FiniteGapConfiguration` for `A + K` at `Q`. -/
theorem theorem8_2_sinTwoTheta_perturbation_complex
    {A K : H →L[ℂ] H} (hA : A.IsSymmetric) (hK : K.IsSymmetric)
    {P Q : Submodule ℂ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : A.Reduces P) :
    delta * ‖DavisKahanExt.sinTwoAngleOperator Q P‖ ≤ 2 * ‖K‖ := by
  have hA0 : (A + K).IsSymmetric := hA.add hK
  have hQred : ContinuousLinearMap.Reduces (A + K) Q := ⟨hQ.invariant, hQperp.invariant⟩
  have hfinite : Foundation.FiniteGapConfiguration (A + K) Q delta := ⟨beta, alpha, hab, hQ, hQperp⟩
  have h := sinTwoTheta_perturbation (A := A + K) (B := A) hA0 hQred hPred hdelta hfinite
  have hdiff : ‖A - (A + K)‖ = ‖K‖ := by
    rw [show A - (A + K) = -K by abel, norm_neg]
  rwa [hdiff] at h

/-- **The `sin 2Θ` estimate at Theorem 8.2's hypotheses, residual form.**

`δ ‖sin 2Θ‖ ≤ 2 ‖R‖` with `R` the printed residual (1.8),
`R = (A + H) E₀ - E₀ A₀`.  Inherited from `sinTwoTheta_residual`; the trial
embedding is the inclusion `E₀ = P.subtypeL`, whose range is `P`.

The printed inequality is written at the *directed* `Θ₀`; the conclusion below is
at the **ambient** `sinTwoAngleOperator Q P`.  At the operator norm that is
legitimate and is the stronger reading, because `norm_offdiag_add_eq` makes the
two off-diagonal blocks of the reflection defect equal there.  It is not
legitimate at a general unitarily invariant norm, and that is the remaining open
axis recorded at the head of section 2b below. -/
theorem theorem8_2_sinTwoTheta_residual_complex
    {A K : H →L[ℂ] H} (hA : A.IsSymmetric) (hK : K.IsSymmetric)
    {P Q : Submodule ℂ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (_hPred : A.Reduces P) :
    delta * ‖DavisKahanExt.sinTwoAngleOperator Q P‖ ≤
      2 * ‖residual (A + K) P.subtypeL (compressOperator P A)‖ := by
  classical
  have hA0 : (A + K).IsSymmetric := hA.add hK
  have hQred : ContinuousLinearMap.Reduces (A + K) Q := ⟨hQ.invariant, hQperp.invariant⟩
  have hfinite : Foundation.FiniteGapConfiguration (A + K) Q delta := ⟨beta, alpha, hab, hQ, hQperp⟩
  have hrange : LinearMap.range (P.subtypeL : P →L[ℂ] H).toLinearMap = P := by
    ext x
    simp
  have : (LinearMap.range (P.subtypeL : P →L[ℂ] H).toLinearMap).HasOrthogonalProjection := by
    rw [hrange]; infer_instance
  have hX : IsometricEmbedding (P.subtypeL : P →L[ℂ] H) := fun x => rfl
  have hM : (compressOperator P A).IsSymmetric := by
    intro x y
    change ⟪compressOperator P A x, y⟫_ℂ = ⟪x, compressOperator P A y⟫_ℂ
    have := hA (x : H) (y : H)
    simpa [compressOperator, Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr y.2,
      Submodule.starProjection_eq_self_iff.mpr x.2] using this
  have h := sinTwoTheta_residual (A := A + K) hA0 hQred (P.subtypeL : P →L[ℂ] H) hX
    hM hdelta hfinite
  have hangle : sinTwoThetaEmbedding Q (P.subtypeL : P →L[ℂ] H) =
      DavisKahanExt.sinTwoAngleOperator Q P := by
    rw [sinTwoThetaEmbedding_eq_rangeAngle Q (P.subtypeL : P →L[ℂ] H) hX]
    congr 1
    simp only [hrange]
  rwa [hangle] at h

/-! ### 2b. The same `sin 2Θ` estimate at every source unitarily invariant norm

The printed `sin 2Θ` theorem concludes "for every unitary-invariant norm", so
that is the scope at which Theorem 8.2 inherits it; the two theorems above are
its operator-norm reading.  The perturbation alternative is restated here over
the paper's own class `SymmetricNormingFunction`, inherited from equation (7.5)
(`DavisKahan1970.sinTwoTheta_ambient_bounded_symmetricNorming_complex`) with nothing re-proved.

The conclusion names the paper's literal `sin 2Θ`, the positive operator
`sinTwoAngleOperatorC Q P`, rather than the modulus-free
`sinTwoAngleOperator` of the operator-norm statements; the two have the same
operator norm by `norm_sinTwoAngleOperatorC_eq_norm_directedSinTwoAngleOperatorC`,
but only the former carries the whole singular-value list that a general
unitarily invariant norm reads.

## The residual alternative at this scope: the obstruction, and how it was passed

**CORRECTED 2026-08-11.**  This passage used to be headed "Why the residual
alternative is not here" and concluded that the printed constant `2` was out of
reach at a general unitarily invariant norm.  It is contradicted by
`theorem8_2_sinTwoTheta_residual_symmetricNorming` below, which is here and
which carries the printed `2`.  The measurement itself was correct and is kept;
what was wrong was the inference drawn from it, because it measured the
**ambient** reading and the printed statement is the **directed** one.

*The measurement, which stands.*  The printed residual conclusion is
`δ‖sin 2Θ₀‖ ≤ 2‖R‖` at the **directed** `Θ₀` (and the paper's own proof of it,
through Lemma 6.1, actually gives the constant `1`).
`theorem8_2_sinTwoTheta_residual_complex` above states it at the **ambient** `Θ`,
which is legitimate at the operator norm because the two off-diagonal blocks of
the reflection defect have the *same* operator norm -- that is
`norm_offdiag_add_eq`.  For a general unitarily invariant norm that identity
fails.  Writing `C` for the `P`-to-`Pᗮ` block of `A + K`, the singular values of
`C + C⋆` are those of `C` doubled, so a symmetric gauge sees
`N(C + C⋆) = 2 N(C)` in general (the trace norm does).  Every route through
`sinTwoTheta_ambient_bounded_symmetricNorming_complex` has to supply a comparison operator reduced
by `P`, i.e. block-diagonal, so its displacement from `A + K` is exactly
`-(C + C⋆)` for the best such choice; with `N(C) ≤ N(R)` this yields the
constant `4`, not the printed `2`.  So the **ambient** `sin 2Θ` at a general
symmetric gauge is still not available with the printed constant, and no
statement below claims it.

*What the inference got wrong.*  The passage then asserted that recovering the
printed constant needs the singular-value identification of `sin 2Θ₀` with
`sin 2Θ₁` -- the paper's `S_0`/`S_1` discussion, i.e. the Halmos generic
decomposition.  It does not.  The printed conclusion is about `Θ₀`, so the route
that works never forms the ambient sum at all: prove the estimate at the
directed block `sinTwoThetaIdealBlock Q P`, and the constant `2` comes
out of `sinTwoTheta_directed_boundedResidual_blockRepresentative_symmetricNorming_complex`'s own chain -- the paper
projection block dominates `δ` times the ideal block, the block defect costs the
factor `2`, and the residual is extended by zero along `P.subtypeL.adjoint`,
which preserves the whole approximation-singular sequence and hence every paper
norm.  No generic decomposition is used anywhere in it.

*What is therefore available below.*
`theorem8_2_sinTwoTheta_residual_all_kyFan` at every Ky Fan level and
`theorem8_2_sinTwoTheta_residual_symmetricNorming` at every norm in the
paper's own class, both at the directed `sin 2Θ₀` and both with the printed
factor `2`.  The block is the proof's statement;
`theorem8_2_sinTwoTheta_residual_directedAngle_symmetricNorming` moves it onto
the paper's own trial-side directed angle, which is a theorem rather than a
rewriting -- see its docstring.  The negative knowledge that survives is exactly one sentence: the
**ambient** `sin 2Θ` reading of the residual alternative does not reach the
printed constant at a general symmetric gauge, and is available only at the
operator norm. -/

omit [CompleteSpace H] in
/-- **The spectral dictionary between Section 8 and the `sin 2Θ` development.**

Section 8 states its spectral placements with `Foundation.SpectrumIn`, which
constrains `restrictedSpectrum`; the `sin 2Θ` development states them as
`spectrum ℝ (compressOperator …)`.  On an invariant subspace the compression is
the honest restriction (`compressOperator_eq_restrict_of_invariant`), and over
`ℂ` the real Banach-algebra spectrum is the pulled-back complex spectrum
(`realSpectrum_eq_spectrum_real`), so the two readings agree. -/
theorem spectrum_compressOperator_subset_of_spectrumIn
    {T : H →L[ℂ] H} {U : Submodule ℂ H} [U.HasOrthogonalProjection]
    {s : Set ℝ} (h : Foundation.SpectrumIn T U s) :
    spectrum ℝ (compressOperator U T) ⊆ s := by
  intro r hr
  refine h.subset ⟨h.invariant, ?_⟩
  rw [compressOperator_eq_restrict_of_invariant T U h.invariant] at hr
  exact (realSpectrum_eq_spectrum_real
    (T.restrict h.invariant)).ge hr

/-- **The `sin 2Θ` estimate at Theorem 8.2's hypotheses, perturbation form, for
every source unitarily invariant norm.**

`δ ‖sin 2Θ‖ ≤ 2 ‖H‖`, at the paper's own class of unitarily invariant norms and
at Theorem 8.2's own hypotheses.  `theorem8_2_sinTwoTheta_perturbation_complex`
is the operator-norm reading of the same inheritance.

Nothing is re-proved.  This is equation (7.5) of the paper's Section 7,
`DavisKahan1970.sinTwoTheta_ambient_bounded_symmetricNorming_complex`, read with `A + K` carrying
the printed gap on `Q` and with `A` — which `P` reduces by hypothesis — as the
comparison operator, so that the displacement is `-K`. -/
theorem theorem8_2_sinTwoTheta_perturbation_symmetricNorming
    (N : ExactSinTheta.SymmetricNormingFunction)
    {A K : H →L[ℂ] H} (hA : A.IsSymmetric) (hK : K.IsSymmetric)
    {P Q : Submodule ℂ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : A.Reduces P)
    (hKmem : N.Mem K) :
    N.Mem (sinTwoAngleOperatorC Q P) ∧
      delta * N.gauge (sinTwoAngleOperatorC Q P) ≤ 2 * N.gauge K := by
  have hAsa : IsSelfAdjoint A :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA
  have hKsa : IsSelfAdjoint K :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hK
  have hAKsa : IsSelfAdjoint (A + K) := hAsa.add hKsa
  have hQred : ContinuousLinearMap.Reduces (A + K) Q := ⟨hQ.invariant, hQperp.invariant⟩
  have hUspec : spectrum ℝ (compressOperator Q (A + K)) ⊆ Set.Icc beta alpha :=
    spectrum_compressOperator_subset_of_spectrumIn hQ
  have hUspec' : ∀ x ∈ spectrum ℝ (compressOperator Qᗮ (A + K)),
      x ≤ beta - delta ∨ alpha + delta ≤ x :=
    fun _ hx => spectrum_compressOperator_subset_of_spectrumIn hQperp hx
  have hneg : A - (A + K) = (-1 : ℂ) • K := by
    rw [neg_one_smul]
    abel
  have hone : ‖(-1 : ℂ)‖ = 1 := by norm_num
  have hMemNeg : N.Mem (A - (A + K)) := by
    rw [hneg]
    intro htop
    rw [N.extendedGauge_smul, hone] at htop
    rcases ENNReal.mul_eq_top.mp htop with ⟨_, h⟩ | ⟨h, _⟩
    · exact hKmem h
    · exact absurd h (by simp)
  have hgaugeNeg : N.gauge (A - (A + K)) = N.gauge K := by
    rw [hneg, N.gauge_smul _ hKmem, hone, one_mul]
  obtain ⟨hmem, hle⟩ := DavisKahan1970.sinTwoTheta_ambient_bounded_symmetricNorming_complex N
    hAKsa hAsa hQred hPred hdelta hab hUspec hUspec' hMemNeg
  exact ⟨hmem, by rwa [hgaugeNeg] at hle⟩

/-- **Theorem 8.2's residual `sin 2Θ₀` inequality at every Ky Fan
level.**  This is the directed norm content the printed residual alternative
inherits from the Section 2 `sin 2Θ` theorem. -/
theorem theorem8_2_sinTwoTheta_residual_all_kyFan
    {A K : H →L[ℂ] H} (hA : A.IsSymmetric) (hK : K.IsSymmetric)
    {P Q : Submodule ℂ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (_hPred : A.Reduces P) :
    ∀ k : ℕ,
      delta * kyFanApproximationGauge k
          (TauCeti.DavisKahan.sinTwoThetaIdealBlock Q P) ≤
        2 * kyFanApproximationGauge k
          (residual (A + K) P.subtypeL (compressOperator P A)) := by
  have hAsa : IsSelfAdjoint A :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA
  have hKsa : IsSelfAdjoint K :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hK
  have hAKsa : IsSelfAdjoint (A + K) := hAsa.add hKsa
  have hQred : ContinuousLinearMap.Reduces (A + K) Q := ⟨hQ.invariant, hQperp.invariant⟩
  have hUspec : spectrum ℝ (compressOperator Q (A + K)) ⊆ Set.Icc beta alpha :=
    spectrum_compressOperator_subset_of_spectrumIn hQ
  have hUspec' : ∀ x ∈ spectrum ℝ (compressOperator Qᗮ (A + K)),
      x ≤ beta - delta ∨ alpha + delta ≤ x :=
    fun _ hx => spectrum_compressOperator_subset_of_spectrumIn hQperp hx
  exact DavisKahan1970.sinTwoTheta_directed_boundedResidual_blockRepresentative_kyFan_complex
    (A := A + K) (U := Q) (V := P)
    hAKsa hQred hdelta hab hUspec hUspec' (compressOperator P A)

/-- **Theorem 8.2's residual alternative for every source unitarily invariant
norm, in the proof's block form.**

The conclusion is on `sinTwoThetaIdealBlock Q P`, the one-sided block the
estimate is actually proved about -- not the ambient `sin 2Θ`, which at general
symmetric gauges carries the same nonzero singular data twice, and not the
paper's directed angle, which is an *ordered* object in the opposite ordering.
`theorem8_2_sinTwoTheta_residual_directedAngle_symmetricNorming` is the
source-facing statement, and it is what this row's canonical evidence names. -/
theorem theorem8_2_sinTwoTheta_residual_symmetricNorming
    (N : ExactSinTheta.SymmetricNormingFunction)
    {A K : H →L[ℂ] H} (hA : A.IsSymmetric) (hK : K.IsSymmetric)
    {P Q : Submodule ℂ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (_hPred : A.Reduces P)
    (hRmem : N.Mem (residual (A + K) P.subtypeL (compressOperator P A))) :
    N.Mem (TauCeti.DavisKahan.sinTwoThetaIdealBlock Q P) ∧
      delta * N.gauge (TauCeti.DavisKahan.sinTwoThetaIdealBlock Q P) ≤
        2 * N.gauge (residual (A + K) P.subtypeL (compressOperator P A)) := by
  have hAsa : IsSelfAdjoint A :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA
  have hKsa : IsSelfAdjoint K :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hK
  have hAKsa : IsSelfAdjoint (A + K) := hAsa.add hKsa
  have hQred : ContinuousLinearMap.Reduces (A + K) Q := ⟨hQ.invariant, hQperp.invariant⟩
  have hUspec : spectrum ℝ (compressOperator Q (A + K)) ⊆ Set.Icc beta alpha :=
    spectrum_compressOperator_subset_of_spectrumIn hQ
  have hUspec' : ∀ x ∈ spectrum ℝ (compressOperator Qᗮ (A + K)),
      x ≤ beta - delta ∨ alpha + delta ≤ x :=
    fun _ hx => spectrum_compressOperator_subset_of_spectrumIn hQperp hx
  exact DavisKahan1970.sinTwoTheta_directed_boundedResidual_blockRepresentative_symmetricNorming_complex
    (A := A + K) (U := Q) (V := P) N hAKsa hQred hdelta hab
    hUspec hUspec' (compressOperator P A) hRmem

/-- **Theorem 8.2's printed residual alternative, on the paper's own directed
angle.**

`δ N(sin 2Θ₀) ≤ 2 N(R)` with the conclusion on
`Angle.directedSinTwoAngleOperator P Q` -- the **trial-side** ordering, `P` the
trial subspace carrying the residual and `Q` the subspace whose two blocks the
printed gap separates.  That is what `‖sin Θ₀‖ = ‖Q^⊥ P‖ = ‖Q^⊥ E₀‖` names in
Section 1.

`theorem8_2_sinTwoTheta_residual_symmetricNorming` above proves the same estimate
about `sinTwoThetaIdealBlock Q P`, which is the proof's one-sided block rather
than an angle, and in the opposite ordering of the pair.  Crossing that gap is a
theorem and not a renaming: the two ordered directed *sines* have different
approximation numbers in general.  The doubled sines do not, which is
`Angle.directedSinTwoAngleOperator_hasSameApproximationNumbers_swap`, and the
composite bridge used here is
`Angle.sinTwoThetaIdealBlock_hasSameApproximationNumbers_trialSide`. -/
theorem theorem8_2_sinTwoTheta_residual_directedAngle_symmetricNorming
    (N : ExactSinTheta.SymmetricNormingFunction)
    {A K : H →L[ℂ] H} (hA : A.IsSymmetric) (hK : K.IsSymmetric)
    {P Q : Submodule ℂ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : A.Reduces P)
    (hRmem : N.Mem (residual (A + K) P.subtypeL (compressOperator P A))) :
    N.Mem (Angle.directedSinTwoAngleOperator P Q) ∧
      delta * N.gauge (Angle.directedSinTwoAngleOperator P Q) ≤
        2 * N.gauge (residual (A + K) P.subtypeL (compressOperator P A)) := by
  obtain ⟨hmem, hle⟩ :=
    theorem8_2_sinTwoTheta_residual_symmetricNorming N hA hK hdelta hab hQ hQperp hPred hRmem
  refine ⟨(Angle.mem_directedSinTwoAngleOperator_trialSide_iff _ _ N).mpr hmem, ?_⟩
  rwa [Angle.gauge_directedSinTwoAngleOperator_trialSide]

/-! ### Source-exact façades

The two theorems above are proved for an arbitrary Hilbert space and an arbitrary
symmetric norming function.  The façades below are the printed statement --
separable ambient Hilbert space and the literal `NormalizedUnitaryInvariantNorm`
class -- and are the canonical source evidence for this row's retained
double-angle bounds. -/

/-- **Theorem 8.2's retained perturbation bound, at the printed source scope.** -/
theorem theorem8_2_sinTwoTheta_perturbation_sourceExact
    
    (N : ExactSinTheta.NormalizedUnitaryInvariantNorm.{0, _} ℂ)
    {A K : H →L[ℂ] H} (hA : A.IsSymmetric) (hK : K.IsSymmetric)
    {P Q : Submodule ℂ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : A.Reduces P)
    (hKmem : N.Mem K) :
    N.Mem (sinTwoAngleOperatorC Q P) ∧
      delta * N.gauge (sinTwoAngleOperatorC Q P) ≤ 2 * N.gauge K :=
  TauCeti.DavisKahan1970.normalizedUnitaryInvariant_of_symmetricNorming_mul N hdelta two_pos
    hKmem fun M hM =>
      theorem8_2_sinTwoTheta_perturbation_symmetricNorming M hA hK hdelta hab hQ hQperp
        hPred hM

/-- **Theorem 8.2's retained residual bound on the directed angle, at the printed
source scope.** -/
theorem theorem8_2_sinTwoTheta_residual_directedAngle_sourceExact
    
    (N : ExactSinTheta.NormalizedUnitaryInvariantNorm.{0, _} ℂ)
    {A K : H →L[ℂ] H} (hA : A.IsSymmetric) (hK : K.IsSymmetric)
    {P Q : Submodule ℂ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
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
      theorem8_2_sinTwoTheta_residual_directedAngle_symmetricNorming M hA hK hdelta hab
        hQ hQperp hPred hM

/-! ### 3. The printed conclusion `Θ < π/4` -/

/-- **Davis--Kahan 1970, Theorem 8.2, perturbation alternative, printed form.**

`Θ < π/4` under the printed hypotheses together with the standing convention
(1.5).  The proof adds nothing to `theorem8_2_perturbationHalfGap_complex`; (1.5)
only converts its directed conclusion into the symmetric one. -/
theorem theorem8_2_perturbationHalfGap_maximalAngle_lt [FiniteDimensional ℂ H]
    {A K : H →L[ℂ] H} (hA : A.IsSymmetric) (hK : K.IsSymmetric)
    {P Q : Submodule ℂ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : A.Reduces P)
    (hP : Foundation.SpectrumIn A P (Set.Icc (beta - delta / 2) (alpha + delta / 2)))
    (hrank : finrank ℂ P = finrank ℂ Q)
    (hsmall : ‖K‖ < delta / 2) :
    maximalAngle P Q < Real.pi / 4 :=
  maximalAngle_lt_pi_div_four_of_directedGap_lt hrank
    (theorem8_2_perturbationHalfGap_complex hA hK hdelta hab hQ hQperp hPred hP hsmall)

/-- **Davis--Kahan 1970, Theorem 8.2, residual alternative, printed form.** -/
theorem theorem8_2_residualHalfGap_maximalAngle_lt [FiniteDimensional ℂ H]
    {A K : H →L[ℂ] H} (hA : A.IsSymmetric) (hK : K.IsSymmetric)
    {P Q : Submodule ℂ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : A.Reduces P)
    (hP : Foundation.SpectrumIn A P (Set.Icc (beta - delta / 2) (alpha + delta / 2)))
    (hrank : finrank ℂ P = finrank ℂ Q)
    (hRsmall : ‖residual (A + K) P.subtypeL (compressOperator P A)‖ < delta / 2) :
    maximalAngle P Q < Real.pi / 4 :=
  maximalAngle_lt_pi_div_four_of_directedGap_lt hrank
    (theorem8_2_residualHalfGap_complex hA hK hdelta hab hQ hQperp hPred hP hRsmall)

/-- **Theorem 8.2's printed disjunction, printed conclusion.** -/
theorem theorem8_2_branch_maximalAngle_lt [FiniteDimensional ℂ H]
    {A K : H →L[ℂ] H} (hA : A.IsSymmetric) (hK : K.IsSymmetric)
    {P Q : Submodule ℂ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : A.Reduces P)
    (hP : Foundation.SpectrumIn A P (Set.Icc (beta - delta / 2) (alpha + delta / 2)))
    (hrank : finrank ℂ P = finrank ℂ Q)
    (hsmall : ‖K‖ < delta / 2 ∨
      ‖residual (A + K) P.subtypeL (compressOperator P A)‖ < delta / 2) :
    maximalAngle P Q < Real.pi / 4 :=
  maximalAngle_lt_pi_div_four_of_directedGap_lt hrank
    (theorem8_2_branch hA hK hdelta hab hQ hQperp hPred hP hsmall)

/-- **Davis--Kahan 1970, Theorem 8.2, printed conclusion `Θ < π/4`, in any
dimension, under Section 3's standing assumption (3.5).**

`maximalAngle_lt_pi_div_four_of_crossedDefects` applied to Theorem 8.2's printed
disjunction: either printed smallness alternative, plus (3.5) in its
constructive form, gives the printed symmetric conclusion with **no**
finite-dimensionality and **no** rank hypothesis.  The complex counterpart of
`theorem8_2_branch_real_maximalAngle_lt_of_crossedDefects`, which existed
first only because the real descent needed it. -/
theorem theorem8_2_branch_maximalAngle_lt_of_crossedDefects
    {A K : H →L[ℂ] H} (hA : A.IsSymmetric) (hK : K.IsSymmetric)
    {P Q : Submodule ℂ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : A.Reduces P)
    (hP : Foundation.SpectrumIn A P (Set.Icc (beta - delta / 2) (alpha + delta / 2)))
    (hcross : CrossedDefectsEquivalent P Q)
    (hsmall : ‖K‖ < delta / 2 ∨
      ‖residual (A + K) P.subtypeL (compressOperator P A)‖ < delta / 2) :
    maximalAngle P Q < Real.pi / 4 :=
  maximalAngle_lt_pi_div_four_of_crossedDefects hcross
    (theorem8_2_branch hA hK hdelta hab hQ hQperp hPred hP hsmall)

/-! ### 4. The whole printed theorem -/

/-- **Davis--Kahan 1970, Theorem 8.2.**

> Add to the hypotheses of the `sin 2θ` theorem either `‖H‖₁ < δ/2` or
> `‖R‖₁ < δ/2`, and assume the spectrum of `A₀` lies in
> `[β - δ/2, α + δ/2]`.  Then, in addition to `δ‖sin 2Θ‖ ≤ 2‖H‖` or
> `δ‖sin 2Θ₀‖ ≤ 2‖R‖`, we have `Θ < π/4`.

Every hypothesis below is one of those, plus the Section 1 standing convention
(1.5) in its finite form.  Every conclusion below is one of those: the two
displayed `sin 2Θ` estimates, which Theorem 8.2 inherits and which hold under
either alternative, and the strict quarter angle, which is Theorem 8.2's own
content.

`‖·‖₁` is the bound norm throughout Theorem 8.2, which is what the operator
norms here are. -/
theorem theorem8_2_complex [FiniteDimensional ℂ H]
    {A K : H →L[ℂ] H} (hA : A.IsSymmetric) (hK : K.IsSymmetric)
    {P Q : Submodule ℂ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {alpha beta delta : ℝ} (hdelta : 0 < delta) (hab : beta ≤ alpha)
    (hQ : Foundation.SpectrumIn (A + K) Q (Set.Icc beta alpha))
    (hQperp : Foundation.SpectrumIn (A + K) Qᗮ (gapExterior beta alpha delta))
    (hPred : A.Reduces P)
    (hP : Foundation.SpectrumIn A P (Set.Icc (beta - delta / 2) (alpha + delta / 2)))
    (hrank : finrank ℂ P = finrank ℂ Q)
    (hsmall : ‖K‖ < delta / 2 ∨
      ‖residual (A + K) P.subtypeL (compressOperator P A)‖ < delta / 2) :
    delta * ‖DavisKahanExt.sinTwoAngleOperator Q P‖ ≤ 2 * ‖K‖ ∧
      delta * ‖DavisKahanExt.sinTwoAngleOperator Q P‖ ≤
        2 * ‖residual (A + K) P.subtypeL (compressOperator P A)‖ ∧
      maximalAngle P Q < Real.pi / 4 :=
  ⟨theorem8_2_sinTwoTheta_perturbation_complex hA hK hdelta hab hQ hQperp hPred,
    theorem8_2_sinTwoTheta_residual_complex hA hK hdelta hab hQ hQperp hPred,
    theorem8_2_branch_maximalAngle_lt hA hK hdelta hab hQ hQperp hPred hP
      hrank hsmall⟩

end Section8
end DavisKahan1970
end TauCeti
