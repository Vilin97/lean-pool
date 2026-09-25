/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
module

public import LeanPool.DavisKahan.DavisKahan.All

/-! # Result Semantic Surface -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan 1970 result semantic audit surface

This file is intentionally outside `DavisKahan.All`.  It gives a hostile reviewer a
single compiler-checkable surface for the Lean declarations selected by the maintained
29-result Davis--Kahan 1970 completion inventory.

Each `#check` below is evidence only: the semantic correspondence to the printed source
is recorded in `dev/davis-kahan-1970-formalization-result-inventory.json` and the
human-readable result audit.  The maintained result inventory is terminal; this surface
keeps source-facing headline declarations and their scope companions compiler-visible.

Run:

```bash
lake env lean DavisKahan/Sources/DavisKahan1970/Audits/ResultSemanticSurface.lean
```
-/

namespace TauCeti.DavisKahan1970.Audits

/-! ### Exact audit wrappers for stronger reusable theorem surfaces

These two declarations are intentionally tiny.  They make the semantic specialization
visible in Lean itself when the maintained reusable theorem is stronger or more general
than the paper-facing result.
-/

universe u v

/-- **Theorem 5.1, scalar-generic exact audit wrapper.**

The reusable theorem only needs the left-inverse half of the printed inverse hypothesis.
This wrapper retains both inverse equations and is generic over the scalar field, making
it compiler-visible that the printed Banach-space theorem is covered over both real and
complex scalars. -/
theorem theorem5_1_scalarGeneric_sourceAudit
    {𝕜 : Type u} [NontriviallyNormedField 𝕜]
    {E F : Type v}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {N : (F →L[𝕜] E) → ℝ}
    (hadd : ∀ S T, N (S + T) ≤ N S + N T)
    (hidealL : ∀ (L : E →L[𝕜] E) (T : F →L[𝕜] E),
      N (L ∘L T) ≤ ‖L‖ * N T)
    (hidealR : ∀ (T : F →L[𝕜] E) (R : F →L[𝕜] F),
      N (T ∘L R) ≤ N T * ‖R‖)
    (hNnonneg : ∀ T, 0 ≤ N T)
    {A Ainv : E →L[𝕜] E} {B : F →L[𝕜] F} {X C : F →L[𝕜] E}
    {ρ δ : ℝ}
    (hρ : 0 ≤ ρ) (hδ : 0 < δ)
    (hB : ‖B‖ ≤ ρ)
    (hAinv_left : Ainv ∘L A = ContinuousLinearMap.id 𝕜 E)
    (_hAinv_right : A ∘L Ainv = ContinuousLinearMap.id 𝕜 E)
    (hAinv_norm : ‖Ainv‖ ≤ (ρ + δ)⁻¹)
    (hEq : A ∘L X - X ∘L B = C) :
    δ * N X ≤ N C := by
  exact TauCeti.ContinuousLinearMap.opNorm_le_of_sylvester_of_leftInverse
    hadd hidealL hidealR hNnonneg hAinv_left hρ hδ hAinv_norm hB hEq

/-- **Theorem 5.2, real ordered exact audit wrapper.**

The maintained real theorem accepts the more general `FormBoundedSylvesterGap`.
This wrapper constructs its ordered `A ≥ c + δ > c ≥ B` branch explicitly, so a
reviewer can compare the printed real theorem without mentally specializing the gap sum. -/
theorem theorem5_2_real_ordered_sourceAudit
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (N : TauCeti.DavisKahan.ExactSinTheta.KyFanDominantIdealFamily (𝕜 := ℝ))
    {A : E →ₗ.[ℝ] E}
    {B : F →ₗ.[ℝ] F}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    {X C : F →L[ℝ] E} {c δ : ℝ}
    (hδ : 0 < δ)
    (hAc : TauCeti.LinearPMap.SemiboundedBelow A (c + δ))
    (hBc : TauCeti.LinearPMap.SemiboundedAbove B c)
    (hEq : TauCeti.LinearPMap.SylvesterEquation A B X C)
    (hC : N.Mem C) :
    N.Mem X ∧ δ * N.gauge X ≤ N.gauge C := by
  exact TauCeti.DavisKahan1970.theorem5_2_kyFanDominant_real
    N hA hB hδ
      (TauCeti.DavisKahan.Sylvester.FormBoundedSylvesterGap.leftAboveRightBelow
        c hAc hBc)
      hEq hC


/-! ## Source-exact Section 2 façades

Each of these states its Section 2 clause at the PRINTED scope.  For the
sine-theta façade that means a separable ambient Hilbert space and
`NormalizedSymmetricOperatorIdealFamily`, with the source-wide vacuity convention
spelled directly in the theorem type as `N.Mem sinTheta₀ → N.Mem R → ...`.
The stronger arbitrary-Hilbert `SymmetricNormingFunction` theorem remains
registered separately as a generalization.  The discharge is the source's own
Fan-dominance reduction at (1.11)-(1.13). -/
end TauCeti.DavisKahan1970.Audits

/-! ## The source's norm class: the two Lean quantifiers are equivalent

Section 1 fixes `‖·‖` as an arbitrary normalized unitarily invariant norm and then
declares the criterion it will use: "Fan dominance is used in the strong form:
`‖K‖ ≤ ‖L‖` for every unitary-invariant norm iff the inequality holds for every Ky
Fan norm."

Two Lean objects model that class in this development.  `SymmetricNormingFunction`
is the Gohberg--Krein reading -- a dimension-coherent symmetric gauge, extended to
infinite dimension as the supremum of its singular-value prefixes.
`KyFanDominantIdealFamily` is the axiomatic reading -- a symmetric operator ideal
family with Fan dominance as a field.  Neither exhausts the other as a *type*: the
Calkin-augmented norm `T ↦ ‖T‖ + ‖π(T)‖` is a Fan-dominant unitarily invariant norm
on `B(H)` that agrees with the operator norm on finite-rank operators, so no
symmetric gauge generates it.

The two theorems below show the *estimates* do not care.  Each quantifier is
equivalent to weak Ky Fan majorization, so a bound proved over one holds over the
other -- and a source-facing endpoint stated over `SymmetricNormingFunction`
therefore delivers the printed "for every unitary-invariant norm", including at
norms outside the symmetrically normed ideals. -/

/-! ## S2-sin-theta: Single-angle sine theorem

Status: **TERMINAL EXACT**.

The first name is the public Section 2 short name, now aliasing the ledger-selected
where-defined RClike theorem. The fixed-field aliases are thin specializations; the older
`SymmetricNormingFunction` declarations remain stronger implementation APIs. -/

/-! ## S2-tan-theta: Single-angle tangent theorem

Status: **TERMINAL EXACT** under the accepted nonlocal source interpretation.

The printed Section 2 statement is not locally self-contained: it does not state the
crossed-defect condition (3.5), which the source introduces in Section 3 and then
assumes as standing before proving this theorem in Section 6.  The source-shaped
ambient declarations therefore carry a crossed-defect hypothesis and *conclude*
membership of the tangent operator in the norm's ideal, which is the explicit form of
the paper's own convention that a result is vacuous when a displayed norm fails to
exist.  The reading, its evidence, and the competing literal reading are recorded in
`dev/davis-kahan-1970-formalization-result-inventory.json` under
`nonlocal_source_interpretation`.

The transversality-form declarations assume `‖sin Θ‖ < 1`, which is strictly stronger
than (3.5); they are registered as specializations, not as the source-shaped form.
-/

/-! ## S2-sin-two-theta: Double-angle sine theorem

Status: **TERMINAL EXACT**.  Both fixed-field endpoints take
`FormBoundedSylvesterGap`, so the printed half-infinite gap scope is covered on
both.  The two `spectrumGap` declarations are the earlier complex route, at a
bounded separating interval only; they are supporting evidence, not the
result's canonical witness.

The **ambient** clause is discharged by
`sinTwoTheta_ambient_unbounded_addBounded_symmetricNorming_complex` and its real
sibling, at the same unbounded scope as the directed clause.  The bounded ambient
endpoints below them are their specializations, retained as an alternative proof.

`sinTwoTheta_ambient_unbounded_reflectionPair_symmetricNorming_rclike` is the same
ambient bound at an **arbitrary `RCLike` field**, on the paper's own ambient
double-angle sine.  It is supporting rather than canonical evidence because it
hypothesises `U` and `V` as a reducing subspace and a reflected pair instead of
naming the printed spectral subspaces, whose construction in this tree is
field-specific.  Its signature carries no capability class and no functional
calculus: the real calculus on `E →L[𝕜] E` is a theorem at every `RCLike` field.
-/
-- The canonical ambient witnesses: the gap is on the blocks of the PERTURBED
-- operator relative to `Q`, which is where Section 2 states it.
-- The unperturbed-gap reading, retained as supporting evidence.
-- The four steps of the role reversal.

/-! ### The directed `sin 2Θ` orientation, pinned

`Angle.directedSinTwoAngleOperator` is an **ordered** object, and the directed
Section 2 clause is about one of the two orderings.  A `#check` cannot see that: the
type of `sinTwoTheta_directed_complex` mentions both subspaces, and swapping them
leaves a well-typed theorem with the same name and the same declaration signature
shape.  The audit below fixes the semantic names and states the intended conclusion
literally, so that a later argument swap fails to elaborate here rather than passing
silently.

`trial` is the subspace carrying the printed residual `R = A E₀ - E₀ A₀`; `gapCarrier`
is the subspace whose two reducing restrictions the printed separation `δ` separates.
The paper's `sin Θ₀` is `Q^⊥ E₀` -- the cross-projection with the trial subspace on
the right -- so the conclusion must be on
`directedSinTwoAngleOperator trial gapCarrier`, in that order. -/

open TauCeti.DavisKahan.Sylvester in
/-- **Orientation audit for the directed `sin 2Θ` clause, over `ℂ`.**

Discharged by a bare application of the source theorem with no adapter and no
rewriting, so it holds exactly when that theorem's conclusion is on the trial-side
ordering. -/
theorem sinTwoTheta_directed_orientation_sourceAudit_complex
    {Hc : Type*} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]
    (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction)
    {A : Hc →ₗ.[ℂ] Hc} (hA : IsSelfAdjoint A)
    {trial : Submodule ℂ Hc} [trial.HasOrthogonalProjection]
    {ritz : trial →L[ℂ] trial} {residual : trial →L[ℂ] Hc}
    {gapCarrier : Submodule ℂ Hc} [gapCarrier.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace A gapCarrier)
    (hVdom : ∀ v : trial, (v : Hc) ∈ A.domain)
    (hres : ∀ v : trial, A ⟨(v : Hc), hVdom v⟩ = residual v + ((ritz v : trial) : Hc))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A gapCarrier hred)
      (TauCeti.LinearPMap.reducingRestriction A gapCarrierᗮ hred.orthogonal) δ)
    (hRmem : N.Mem residual) :
    N.Mem (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator trial gapCarrier) ∧
      δ * N.gauge
          (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator trial gapCarrier) ≤
        2 * N.gauge residual :=
  TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_complex
    N hA hred hVdom hres hδ hgap hRmem

open TauCeti.DavisKahan.Sylvester in
/-- **Orientation audit for the directed `sin 2Θ` clause, over `ℝ`.** -/
theorem sinTwoTheta_directed_orientation_sourceAudit_real
    {Er : Type*} [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]
    (N : TauCeti.DavisKahan.ExactSinTheta.SymmetricNormingFunction)
    {A : Er →ₗ.[ℝ] Er} (hA : IsSelfAdjoint A)
    {trial : Submodule ℝ Er} [trial.HasOrthogonalProjection]
    {ritz : trial →L[ℝ] trial} {residual : trial →L[ℝ] Er}
    {gapCarrier : Submodule ℝ Er} [gapCarrier.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace A gapCarrier)
    (hVdom : ∀ v : trial, (v : Er) ∈ A.domain)
    (hres : ∀ v : trial, A ⟨(v : Er), hVdom v⟩ = residual v + ((ritz v : trial) : Er))
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A gapCarrier hred)
      (TauCeti.LinearPMap.reducingRestriction A gapCarrierᗮ hred.orthogonal) δ)
    (hRmem : N.Mem residual) :
    N.Mem (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator trial gapCarrier) ∧
      δ * N.gauge
          (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator trial gapCarrier) ≤
        2 * N.gauge residual :=
  TauCeti.DavisKahan1970.sinTwoTheta_directed_unboundedResidual_reducing_symmetricNorming_real
    N hA hred hVdom hres hδ hgap hRmem

/-- **The two orderings are not the same operator.**

Recorded so that the orientation audits above are read as content rather than
bookkeeping: what makes them necessary is that the *sines* differ.  The doubled
sines agree only at the level of the approximation-number sequence, which is
`directedSinTwoAngleOperator_hasSameApproximationNumbers_swap`, and that is a
theorem about the doubling. -/
example {Hc : Type*} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]
    (U V : Submodule ℂ Hc) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator U V).HasSameApproximationNumbers
      (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator V U) :=
  TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator_hasSameApproximationNumbers_swap U V

/-! ## S2-tan-two-theta: Double-angle tangent theorem

Status: **TERMINAL EXACT**.
-/

/-! ## DK-3.1-prop: Acute direct rotation existence and uniqueness

Status: **TERMINAL EXACT**.
-/

/-! ## DK-3.2-prop: Nonacute existence criterion

Status: **TERMINAL EXACT**.
-/

/-! ## DK-3.3-prop: Principal square-root characterization

Status: **TERMINAL EXACT**.
-/

/-! ## DK-3.4-prop: Square as a direct rotation

Status: **TERMINAL EXACT**.
-/

/-! ## DK-3.1-thm: Classification of pairs of subspaces

Status: **TERMINAL EXACT**.
-/

-- The canonical witness: the invariant on the SOURCE'S OWN angle operators.
-- The same, over a real Hilbert space, on the source's own angle operator.
-- The printed dimension clause as a proposition, and the realizations it produces.
-- The structural cos^2 Theta classification beneath the source-facing statement.

/-! ## DK-3.1-cor: Compact classification by angle eigenvalues

Status: **TERMINAL EXACT**.
-/
-- The canonical Corollary 3.1 witness: the invariant on the source's own ANGLES.

/-! ## DK-3.5-prop: Angle commutation and eigenspace geometry

Status: **TERMINAL EXACT**.

The three printed clauses do not share a scope, and the signatures below show it.  The source
attaches "in the acute case" to the maximal-eigenspace clause only, so the commutation and
eigenvector-angle clauses are stated for the completed direct rotation selected by a
crossed-defect isometry and carry no acuteness hypothesis; the maximality clause keeps it.
-/

/-! ## DK-3.2-cor: Reversal symmetry

Status: **TERMINAL EXACT**.
-/

/-! ## DK-4.1-prop: Pointwise and singular-value extremality of the direct rotation

Status: **TERMINAL EXACT**.
-/

/-! ## DK-4.1-cor: UI-norm minimality of direct rotation displacement

Status: **TERMINAL EXACT**.
-/

/-! ## DK-4.2-prop: Basis-angle square-sum extremality

Status: **TERMINAL EXACT**.
-/

/-! ## DK-4.3-prop: Squared displacement UI-norm minimality

Status: **TERMINAL EXACT**.
-/

/-! ## DK-4.4-prop: Full-displacement counterexamples and Proposition 4.4 as printed

Status: **TERMINAL REFUTED + REPAIR**.
-/

/-! ## DK-5.1-thm: Banach-space Sylvester lower bound

Status: **TERMINAL EXACT**.
-/

/-! ## DK-5.2-thm: Semibounded self-adjoint Sylvester theorem

Status: **TERMINAL EXACT**.
-/

/-! ## DK-5.1-lem: Strong-cutoff convergence of singular values

Status: **TERMINAL EXACT**.

The canonical witnesses are the two fixed-field statements.  `lemma5_1` is generic
over `RCLike 𝕜` and carries `HasApproximationNumberStrongCutoff 𝕜`, a capability
class whose single field is Lemma 5.1 itself; it is a facade over the two proofs
below and is kept as supporting evidence so the generic development can cite one
name.  A registered witness for a printed lemma should not assume that lemma.
-/

/-! ## DK-6.1-lem: Direct-sum UI-norm comparison and converse

Status: **TERMINAL EXACT**.
-/

/-! ## DK-6.2-lem: Reflection-pinch contraction

Status: **TERMINAL EXACT**.
-/

/-! ## DK-6.1-prop: Sine proof, ambient limitation, and symmetric sine theorem

Status: **TERMINAL EXACT**.
-/

/-! ## DK-6.1-thm: Generalized sine theorem

Status: **TERMINAL EXACT**.
-/

/-! ## DK-6.2-thm: Pairwise-gap square-norm sine theorem

Status: **TERMINAL EXACT**.
-/

/-! ## DK-6.3-thm: Tangent proof machinery, Example 6.1, and generalized tangent theorem

Status: **TERMINAL EXACT**.  The canonical witnesses are the two `_exists_`
unbounded-Ritz paper-norm endpoints.  They ask the caller for nothing the printed
theorem does not: an unbounded Ritz pair, an arbitrary reducing complement, the two
ordered form bounds, and a bounded residual.  From those they *derive* the pole
exclusion (no principal angle is right), *construct* a representative with the
paper's approximation numbers `tan θⱼ`, and bound it in every source norm.

The parameterized `_unboundedRitz_` pair below is the same estimate with the
representative and its characterisation supplied by the caller; it is the
implementation the `_exists_` form composes, and remains registered as
correspondence evidence.  The `_unboundedTrial_` pair adds a spectral-gap
hypothesis the printed theorem does not have -- it assumes the perturbed operator
has no spectrum in `(α, α + δ)`, equivalently that the reducing subspace *is* the
spectral subspace below `α` -- and is a specialization, not a witness.
-/

/-! ## DK-6.3-lem: Finite-rank near-maximizer leakage estimate

Status: **TERMINAL EXACT**.
-/

/-! ## DK-8.1-thm: Branch selection and spectral repulsion

Status: **TERMINAL EXACT**.
-/

/-! ## DK-8.2-thm: Smallness selects the acute branch

Status: **TERMINAL EXACT**.
-/

/-! ## 2026-09-06 source-surface façades and the separability sweep -/

/-! ## 2026-09-07 fourth-hostile-review source-scope façades

Theorem 8.1's existence-with-part-(i) clause and the derived block symmetry;
Section 4 on Davis--Kahan's Definition 3.1 direct rotation; Theorem 3.1's
converse and Corollary 3.1's realization at the paper's separable scope; and
Section 6 on the printed separation, the paper's ambient scope, and the
source's definedness convention. -/

/-! ## 2026-09-07 fifth-hostile-review repairs

Lemma 6.1 on the source's own two operators; Theorem 8.1's existence clause and
part (i) as one printed sentence; and parts (ii) and (iii) on the blocks
themselves, with the symmetric gauge at the block dimension. -/

/-! ## An approximation-number extension of Theorem 8.1 (ii)

Part (ii) is printed with "natural infinite-dimensional extensions"; part (iii)
is not.  The phrase does not identify a unique formal proposition -- Section 1
offers both the minimax sequence and spectral-multiplicity language and does not
choose -- so these are registered as generalizations, not as source evidence for
the phrase. -/
