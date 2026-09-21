/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section8.Theorem81Majorization
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section8.Theorem81MajorizationReal
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.AngleGeometry
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Examples

/-! # Theorem81Angle Forms -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan 1970, Theorem 8.1(ii)--(iii): the source dictionary

`Section8PartII.lean` and `Section8PartIII.lean` prove parts (ii) and (iii) about
*ambient operators* -- compressions cut down by a projection, and the ambient
cosine blocks `P_{Qᗮ} P_{Pᗮ}` and `P_Q P_P`.  The printed clauses are about
*eigenvalues* `α_k`, `λ_k` and *principal angles* `θ_k`.  This module compiles
the dictionary between the two readings, so that no part of the correspondence
is left as prose.

## The three identifications

1. **Positive block approximation numbers are ordered eigenvalues.**
   `approximationNumber_eq_eigenvalues_of_isPositive`.  Every block occurring in
   Theorem 8.1(ii)--(iii) is positive -- `A₁ - α ≥ δ` on `Pᗮ`, `(α+δ) - A₀ ≥ δ`
   on `P`, and the same on the branch -- so its approximation numbers are its
   sorted eigenvalues, which is the printed `α_k - α` and `λ_k - α`.

2. **Extension by zero appends zeros.**
   `approximationNumber_upperBlockShift_eq_zero_of_le` and its lower companion.
   The ambient blocks vanish off `Pᗮ` (resp. `P`), so beyond that rank every
   approximation number is `0`.  Since the nonzero entries of a positive block
   are its eigenvalues and the sequence is decreasing, the ambient sequence is
   the printed finite eigenvalue list followed by zeros -- and a zero tail
   changes neither a prefix sum nor a symmetric gauge.

3. **Cosine-block singular values are the principal cosines.**
   `approximationNumber_cosineBlock_eq_principalCosines` and its lower
   companion.  `TauCeti.principalCosines U V` is the repository's principal-angle
   cosine sequence, defined as the singular values of the cross projection
   `P_V P_U`; the ambient `C₁` *is* that cross projection for the pair
   `(Pᗮ, Qᗮ)`, so the identification is definitional once approximation numbers
   and singular values are identified.  No new `θ` is introduced: this is the
   paper's own equation (1.16), `Θ_j = arccos (C_j C_j⋆)^{1/2}`, which defines
   the angles as the arccosines of exactly these numbers.
   `cos_arccos_approximationNumber_cosineBlock` records the round trip
   `cos θ_i = a_i(C₁)` with `θ_i ∈ [0, π/2]`, and
   `norm_cosineBlock_eq_principalCosines_zero` identifies the printed bound norm
   `‖C₁‖₁` with the largest principal cosine.

## Ordering conventions, handled on both sides at once

`ContinuousLinearMap.approximationNumber` and `TauCeti.principalCosines` are
both indexed **decreasingly**.  The paper prints `λ₁ ≤ λ₂ ≤ ⋯` and
`α₁ ≤ α₂ ≤ ⋯` increasing, and (Section 1, after (1.16)) `θ₁ ≥ θ₂ ≥ ⋯`
decreasing, so the printed `cos²θ_k` is *increasing* in `k`.  The printed
right-hand side `(λ_k - α) cos²θ_k` therefore pairs the `k`-th smallest
eigenvalue with the `k`-th smallest squared cosine, which is the same multiset
of products as pairing largest with largest -- what the decreasing Lean indexing
does.

That reindex is not left as a remark.  `Fin.rev` versions of both part (iii)
statements are proved below (`..._rev_source`), and they are the printed
increasing-index reading: **both** sides are reversed, never one.  A symmetric
gauge cannot tell the difference, which is exactly `FiniteSymmetricGauge.perm`
at `TauCeti.FiniteSymmetricGauge.revPerm`.

## The source-facing statements

`theorem8_1_upperApproximationRepulsion_angle` and its lower companion
state part (ii) with the printed factor written as a principal cosine.
`theorem8_1_upperSymmetricGaugeRepulsion_angle` and its lower companion
state part (iii) with the printed right-hand side `(λ_i - α) cos²θ_i`, quantified
over **every** symmetric gauge -- not the operator norm, not the Frobenius norm,
not Ky Fan `k` alone.

## Scalar scope, measured 2026-08-11

The three identifications of sections 1--3, and the opening illustration of the
last section, are stated over an arbitrary `RCLike` field.  The six printed
statements of sections 4--6 are complex, and the obstruction is that they
**name** `canonicalLowBranch`; it is `boundedSelfAdjointSpectralSubspace`, which
is declared for `E →L[ℂ] E` alone, so the statements are not expressible over a
general `𝕜` at all.  This is *not* the `gramSpectralPVM` obstruction that keeps
`approximationNumber_mono_of_form_le` complex; that one is reached only through
the proofs, never through these statements.  See section 0 below.

Not being generically statable over `𝕜` is not the same as not being statable
over `ℝ`.  Section 7 carries the **real** siblings of all six -- the same printed
vocabulary, over `InnerProductSpace ℝ E`, named against `canonicalLowBranchReal`
instead.  They are the real endpoints of `Section8PartIIReal.lean` and
`Section8PartIIIReal.lean` rewritten through the identifications of sections
1--3, which apply at `𝕜 = ℝ` unchanged; no new analysis appears in section 7.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section8

open scoped InnerProductSpace
open TauCeti.DavisKahan
open Module (finrank)

universe u

/-! ### 0. Scalar scope

Sections 1--3 are the identifications, and they hold over **any** `RCLike`
scalar field: `TauCeti.principalCosines` is `𝕜`-generic, the block algebra
(`upperBlockShift`, `cosineBlock`, `lowerBlockShift`, `lowerCosineBlock`) is
`𝕜`-generic in `Section8PartII.lean`'s `section Generic`, and
`approximationNumber = singularValues` in finite dimensions is `𝕜`-generic.

Sections 4--6 are the printed statements, and they are complex.  The obstruction
is *not* the `gramOperator`/`gramSpectralPVM` layer that holds
`approximationNumber_mono_of_form_le` at `ℂ`; that layer is reached only
transitively.  It is that the statements **name** `canonicalLowBranch`, which is
`boundedSelfAdjointSpectralSubspace` and is declared for `E →L[ℂ] E` alone.  The
real reading of parts (ii) and (iii) therefore goes through the separate
`canonicalLowBranchReal` of `Section8PartIIReal.lean`, whose argument list is
not the complex one -- it carries the printed hypotheses, because the spectral
repulsion that selects the branch must be proved before the branch exists.  A
single `𝕜`-generic statement of sections 4--6 would need a `𝕜`-generic bounded
spectral subspace, which does not exist here; see `section ComplexBranch` below.

Section 7 states the real half over `canonicalLowBranchReal`.  It is a sibling
family and not a generalization: the two branches take different arguments, so
no single statement covers both, and that is the whole of the obstruction.
-/

section Generic

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-! ### 1. Positive blocks: approximation numbers are ordered eigenvalues -/

omit [CompleteSpace H] in
/-- **A positive operator's approximation numbers are its sorted eigenvalues.**

In finite dimensions the approximation numbers are the singular values, and for
a positive operator the singular values are the eigenvalues.  This is the step
that turns the ambient part (ii)/(iii) statements into the printed `α_k`, `λ_k`
readings, since every block appearing there is positive. -/
theorem approximationNumber_eq_eigenvalues_of_isPositive [FiniteDimensional 𝕜 H]
    {S : H →L[𝕜] H} (hpos : (S : H →ₗ[𝕜] H).IsPositive)
    (i : Fin (finrank 𝕜 H)) :
    S.approximationNumber (i : ℕ) = hpos.isSymmetric.eigenvalues rfl i := by
  rw [ContinuousLinearMap.approximationNumber_eq_singularValues,
    ← ContinuousLinearMap.toLinearMap_singularValues]
  exact TauCeti.singularValues_of_isPositive hpos i

omit [CompleteSpace H] in
/-- The positivity of an ambient block in the form `approximationNumber_eq_eigenvalues_of_isPositive`
consumes. -/
theorem isPositive_toLinearMap_of_nonneg {S : H →L[𝕜] H}
    (hS : (0 : H →L[𝕜] H) ≤ S) : (S : H →ₗ[𝕜] H).IsPositive :=
  ((ContinuousLinearMap.nonneg_iff_isPositive S).mp hS).toLinearMap

/-! ### 2. Extension by zero appends zeros -/

omit [CompleteSpace H] in
/-- The unperturbed upper block lives on `Pᗮ`. -/
theorem range_upperBlockShift_le (A : H →L[𝕜] H) (P : Submodule 𝕜 H)
    [P.HasOrthogonalProjection] (alpha : ℝ) :
    LinearMap.range (upperBlockShift A P alpha : H →ₗ[𝕜] H) ≤ Pᗮ := by
  rintro y ⟨x, rfl⟩
  exact Submodule.starProjection_apply_mem _ _

omit [CompleteSpace H] in
/-- The unperturbed lower block lives on `P`. -/
theorem range_lowerBlockShift_le (A : H →L[𝕜] H) (P : Submodule 𝕜 H)
    [P.HasOrthogonalProjection] (alpha delta : ℝ) :
    LinearMap.range (lowerBlockShift A P alpha delta : H →ₗ[𝕜] H) ≤ P := by
  rintro y ⟨x, rfl⟩
  exact Submodule.starProjection_apply_mem _ _

omit [CompleteSpace H] in
/-- **Extending the upper compression by zero only appends zeros.**  Beyond the
rank of `Pᗮ` every approximation number of the ambient block vanishes, so the
ambient decreasing sequence is the printed eigenvalue list of `A₁ - α` followed
by zeros. -/
theorem approximationNumber_upperBlockShift_eq_zero_of_le [FiniteDimensional 𝕜 H]
    (A : H →L[𝕜] H) (P : Submodule 𝕜 H) [P.HasOrthogonalProjection]
    (alpha : ℝ) {n : ℕ} (hn : finrank 𝕜 (Pᗮ : Submodule 𝕜 H) ≤ n) :
    (upperBlockShift A P alpha).approximationNumber n = 0 :=
  ContinuousLinearMap.approximationNumber_eq_zero_of_finrank_range_le _
    ((Submodule.finrank_mono (range_upperBlockShift_le A P alpha)).trans hn)

omit [CompleteSpace H] in
/-- **Extending the lower compression by zero only appends zeros.** -/
theorem approximationNumber_lowerBlockShift_eq_zero_of_le [FiniteDimensional 𝕜 H]
    (A : H →L[𝕜] H) (P : Submodule 𝕜 H) [P.HasOrthogonalProjection]
    (alpha delta : ℝ) {n : ℕ} (hn : finrank 𝕜 P ≤ n) :
    (lowerBlockShift A P alpha delta).approximationNumber n = 0 :=
  ContinuousLinearMap.approximationNumber_eq_zero_of_finrank_range_le _
    ((Submodule.finrank_mono (range_lowerBlockShift_le A P alpha delta)).trans hn)

/-! ### 3. Cosine blocks and principal angles -/

omit [CompleteSpace H] in
/-- **The upper cosine block's singular values are the principal cosines of the
pair `(Pᗮ, Qᗮ)`.**

`TauCeti.principalCosines U V` is *defined* as the singular values of the cross
projection `P_V P_U`, and the ambient `C₁ = P_{Qᗮ} P_{Pᗮ}` is that cross
projection.  With `approximationNumber = singularValues` in finite dimensions,
the identification is definitional. -/
theorem approximationNumber_cosineBlock_eq_principalCosines [FiniteDimensional 𝕜 H]
    (P Q : Submodule 𝕜 H) [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (i : ℕ) :
    (cosineBlock P Q).approximationNumber i = TauCeti.principalCosines Pᗮ Qᗮ i := by
  rw [ContinuousLinearMap.approximationNumber_eq_singularValues,
    ← ContinuousLinearMap.toLinearMap_singularValues]
  rfl

omit [CompleteSpace H] in
/-- **The lower cosine block's singular values are the principal cosines of the
pair `(P, Q)`.** -/
theorem approximationNumber_lowerCosineBlock_eq_principalCosines
    [FiniteDimensional 𝕜 H]
    (P Q : Submodule 𝕜 H) [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (i : ℕ) :
    (lowerCosineBlock P Q).approximationNumber i = TauCeti.principalCosines P Q i := by
  rw [ContinuousLinearMap.approximationNumber_eq_singularValues,
    ← ContinuousLinearMap.toLinearMap_singularValues]
  rfl

omit [CompleteSpace H] in
/-- A cosine block is a contraction: it is a composite of two orthogonal
projections. -/
theorem norm_cosineBlock_le_one (P Q : Submodule 𝕜 H)
    [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection] :
    ‖cosineBlock P Q‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  calc ‖cosineBlock P Q x‖ = ‖Qᗮ.starProjection (Pᗮ.starProjection x)‖ := rfl
    _ ≤ ‖Pᗮ.starProjection x‖ := Submodule.norm_starProjection_apply_le _ _
    _ ≤ ‖x‖ := Submodule.norm_starProjection_apply_le _ _
    _ = 1 * ‖x‖ := (one_mul _).symm

omit [CompleteSpace H] in
/-- Every principal cosine of the upper pair lies in `[0, 1]`, so the printed
angle `θ_i = arccos (a_i C₁)` of equation (1.16) is a genuine angle in
`[0, π/2]` and satisfies `cos θ_i = a_i(C₁)`. -/
theorem cos_arccos_approximationNumber_cosineBlock [FiniteDimensional 𝕜 H]
    (P Q : Submodule 𝕜 H) [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (i : ℕ) :
    Real.cos (Real.arccos ((cosineBlock P Q).approximationNumber i)) =
      (cosineBlock P Q).approximationNumber i :=
  Real.cos_arccos
    (by linarith [ContinuousLinearMap.approximationNumber_nonneg (cosineBlock P Q) i])
    ((ContinuousLinearMap.approximationNumber_le_norm _ i).trans
      (norm_cosineBlock_le_one P Q))

omit [CompleteSpace H] in
/-- **The printed bound norm `‖C₁‖₁` is the largest principal cosine.**

The approximation-number sequence starts at the operator norm, so part (ii)'s
factor `‖C₁‖₁²` is `cos²θ_min` -- the cosine of the *smallest* principal angle,
which is the printed reading of replacing every `cos²θ_k` by the largest one. -/
theorem norm_cosineBlock_eq_principalCosines_zero [FiniteDimensional 𝕜 H]
    (P Q : Submodule 𝕜 H) [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection] :
    ‖cosineBlock P Q‖ = TauCeti.principalCosines Pᗮ Qᗮ 0 := by
  rw [← approximationNumber_cosineBlock_eq_principalCosines,
    ContinuousLinearMap.approximationNumber_index_zero]

omit [CompleteSpace H] in
/-- The lower companion: `‖C₀‖₁` is the largest principal cosine of `(P, Q)`. -/
theorem norm_lowerCosineBlock_eq_principalCosines_zero [FiniteDimensional 𝕜 H]
    (P Q : Submodule 𝕜 H) [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection] :
    ‖lowerCosineBlock P Q‖ = TauCeti.principalCosines P Q 0 := by
  rw [← approximationNumber_lowerCosineBlock_eq_principalCosines,
    ContinuousLinearMap.approximationNumber_index_zero]

end Generic

/-! ### 4. Part (ii) with the printed angle factor

Everything from here to the end of `section Source` names `canonicalLowBranch`,
the bounded self-adjoint spectral subspace, and is complex for that reason
alone -- the same reason `Section8PartII.lean` splits at `section ComplexBranch`.
The real reading of these six statements is not a scalar generalization of them;
it is the `_real` family of `Section8PartIIReal.lean` and `Section8PartIIIReal.lean`,
built on `canonicalLowBranchReal`. -/

section Source

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable (A K : H →L[ℂ] H) (P : Submodule ℂ H) [P.HasOrthogonalProjection]
variable {alpha delta : ℝ}

/-- **Theorem 8.1(ii), upper block, with the printed factor as a cosine.**

  `α_k - α ≤ cos²θ_max · (λ_k - α)`,

which is the printed `α_k - α ≤ ‖C₁‖₁² (λ_k - α)` with `‖C₁‖₁` rewritten as the
largest principal cosine of the pair `(Pᗮ, Qᗮ)`. -/
theorem theorem8_1_upperApproximationRepulsion_angle [FiniteDimensional ℂ H]
    (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P)
    (n : ℕ) :
    (upperBlockShift A P alpha).approximationNumber n ≤
      TauCeti.principalCosines Pᗮ (canonicalLowBranch (A + K)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
            (hA.add hK)) alpha)ᗮ 0 ^ 2 *
        (upperBlockShift (A + K) (canonicalLowBranch (A + K)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
            (hA.add hK)) alpha) alpha).approximationNumber n := by
  rw [← norm_cosineBlock_eq_principalCosines_zero]
  exact theorem8_1_upperApproximationRepulsion A K P hdelta hA hK hAP hPlow
    hPhigh hKP hKPperp n

/-- **Theorem 8.1(ii), lower block, with the printed factor as a cosine.** -/
theorem theorem8_1_lowerApproximationRepulsion_angle [FiniteDimensional ℂ H]
    (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P)
    (n : ℕ) :
    (lowerBlockShift A P alpha delta).approximationNumber n ≤
      TauCeti.principalCosines P (canonicalLowBranch (A + K)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
            (hA.add hK)) alpha) 0 ^ 2 *
        (lowerBlockShift (A + K) (canonicalLowBranch (A + K)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
            (hA.add hK)) alpha) alpha delta).approximationNumber n := by
  rw [← norm_lowerCosineBlock_eq_principalCosines_zero]
  exact theorem8_1_lowerApproximationRepulsion A K P hdelta hA hK hAP hPlow
    hPhigh hKP hKPperp n

/-! ### 5. Part (iii) with the printed angle sequence -/

/-- **Theorem 8.1(iii), upper block, printed form.**

  `Φ(α₁ - α, …, α_n - α) ≤ Φ((λ₁ - α) cos²θ₁, …, (λ_n - α) cos²θ_n)`

for **every** symmetric gauge `Φ`, with `cos θ_i` the principal cosines of the
pair `(Pᗮ, Qᗮ)` -- the singular values of the printed `C₁`, by equation (1.16).
Indices run decreasingly; see `theorem8_1_upperSymmetricGaugeRepulsion_angle_rev`
for the printed increasing reading. -/
theorem theorem8_1_upperSymmetricGaugeRepulsion_angle [FiniteDimensional ℂ H]
    (Phi : FiniteSymmetricGauge (finrank ℂ H))
    (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P) :
    Phi (fun i : Fin (finrank ℂ H) =>
        (upperBlockShift A P alpha).approximationNumber (i : ℕ))
      ≤ Phi (fun i : Fin (finrank ℂ H) =>
        (upperBlockShift (A + K) (canonicalLowBranch (A + K)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
              (hA.add hK)) alpha) alpha).approximationNumber (i : ℕ) *
          TauCeti.principalCosines Pᗮ (canonicalLowBranch (A + K)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
              (hA.add hK)) alpha)ᗮ (i : ℕ) ^ 2) := by
  have hrw : (fun i : Fin (finrank ℂ H) =>
      (upperBlockShift (A + K) (canonicalLowBranch (A + K)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
            (hA.add hK)) alpha) alpha).approximationNumber (i : ℕ) *
        TauCeti.principalCosines Pᗮ (canonicalLowBranch (A + K)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
            (hA.add hK)) alpha)ᗮ (i : ℕ) ^ 2) =
      (fun i : Fin (finrank ℂ H) =>
        (upperBlockShift (A + K) (canonicalLowBranch (A + K)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
              (hA.add hK)) alpha) alpha).approximationNumber (i : ℕ) *
          (cosineBlock P (canonicalLowBranch (A + K)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
              (hA.add hK)) alpha)).approximationNumber (i : ℕ) ^ 2) := by
    funext i
    rw [approximationNumber_cosineBlock_eq_principalCosines]
  rw [hrw]
  exact theorem8_1_upperSymmetricGaugeRepulsion Phi A K P hdelta hA hK hAP
    hPlow hPhigh hKP hKPperp

/-- **Theorem 8.1(iii), lower block, printed form.**  The printed "with a
similar relation for `Λ₀`", for every symmetric gauge, with the principal
cosines of `(P, Q)`. -/
theorem theorem8_1_lowerSymmetricGaugeRepulsion_angle [FiniteDimensional ℂ H]
    (Phi : FiniteSymmetricGauge (finrank ℂ H))
    (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P) :
    Phi (fun i : Fin (finrank ℂ H) =>
        (lowerBlockShift A P alpha delta).approximationNumber (i : ℕ))
      ≤ Phi (fun i : Fin (finrank ℂ H) =>
        (lowerBlockShift (A + K) (canonicalLowBranch (A + K)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
              (hA.add hK)) alpha) alpha delta).approximationNumber (i : ℕ) *
          TauCeti.principalCosines P (canonicalLowBranch (A + K)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
              (hA.add hK)) alpha) (i : ℕ) ^ 2) := by
  have hrw : (fun i : Fin (finrank ℂ H) =>
      (lowerBlockShift (A + K) (canonicalLowBranch (A + K)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
            (hA.add hK)) alpha) alpha delta).approximationNumber (i : ℕ) *
        TauCeti.principalCosines P (canonicalLowBranch (A + K)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
            (hA.add hK)) alpha) (i : ℕ) ^ 2) =
      (fun i : Fin (finrank ℂ H) =>
        (lowerBlockShift (A + K) (canonicalLowBranch (A + K)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
              (hA.add hK)) alpha) alpha delta).approximationNumber (i : ℕ) *
          (lowerCosineBlock P (canonicalLowBranch (A + K)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
              (hA.add hK)) alpha)).approximationNumber (i : ℕ) ^ 2) := by
    funext i
    rw [approximationNumber_lowerCosineBlock_eq_principalCosines]
  rw [hrw]
  exact theorem8_1_lowerSymmetricGaugeRepulsion Phi A K P hdelta hA hK hAP
    hPlow hPhigh hKP hKPperp

/-! ### 6. The printed increasing index, by a global reindex

The paper prints its eigenvalues increasingly and its angles decreasingly; the
repository indexes both decreasingly.  The wrappers below apply `Fin.rev` to
**both** sides at once, which is a global reindex and not a reordering of one
side against the other.  They are the printed reading of part (iii), and they
follow from the decreasing statements by permutation invariance alone. -/

/-- **Theorem 8.1(iii), upper block, in the paper's index order.**  Both sides
are reindexed by `Fin.rev` together. -/
theorem theorem8_1_upperSymmetricGaugeRepulsion_angle_rev
    [FiniteDimensional ℂ H]
    (Phi : FiniteSymmetricGauge (finrank ℂ H))
    (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P) :
    Phi (fun i : Fin (finrank ℂ H) =>
        (upperBlockShift A P alpha).approximationNumber (i.rev : ℕ))
      ≤ Phi (fun i : Fin (finrank ℂ H) =>
        (upperBlockShift (A + K) (canonicalLowBranch (A + K)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
              (hA.add hK)) alpha) alpha).approximationNumber (i.rev : ℕ) *
          TauCeti.principalCosines Pᗮ (canonicalLowBranch (A + K)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
              (hA.add hK)) alpha)ᗮ (i.rev : ℕ) ^ 2) := by
  have hL := Phi.perm (fun i : Fin (finrank ℂ H) =>
    (upperBlockShift A P alpha).approximationNumber (i : ℕ))
    (FiniteSymmetricGauge.revPerm (finrank ℂ H))
  have hR := Phi.perm (fun i : Fin (finrank ℂ H) =>
    (upperBlockShift (A + K) (canonicalLowBranch (A + K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
          (hA.add hK)) alpha) alpha).approximationNumber (i : ℕ) *
      TauCeti.principalCosines Pᗮ (canonicalLowBranch (A + K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
          (hA.add hK)) alpha)ᗮ (i : ℕ) ^ 2)
    (FiniteSymmetricGauge.revPerm (finrank ℂ H))
  rw [show (fun i : Fin (finrank ℂ H) =>
      (upperBlockShift A P alpha).approximationNumber (i.rev : ℕ)) =
      (fun i : Fin (finrank ℂ H) =>
        (upperBlockShift A P alpha).approximationNumber (i : ℕ)) ∘
        (FiniteSymmetricGauge.revPerm (finrank ℂ H)) from rfl,
    show (fun i : Fin (finrank ℂ H) =>
      (upperBlockShift (A + K) (canonicalLowBranch (A + K)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
            (hA.add hK)) alpha) alpha).approximationNumber (i.rev : ℕ) *
        TauCeti.principalCosines Pᗮ (canonicalLowBranch (A + K)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
            (hA.add hK)) alpha)ᗮ (i.rev : ℕ) ^ 2) =
      (fun i : Fin (finrank ℂ H) =>
        (upperBlockShift (A + K) (canonicalLowBranch (A + K)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
              (hA.add hK)) alpha) alpha).approximationNumber (i : ℕ) *
          TauCeti.principalCosines Pᗮ (canonicalLowBranch (A + K)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
              (hA.add hK)) alpha)ᗮ (i : ℕ) ^ 2) ∘
        (FiniteSymmetricGauge.revPerm (finrank ℂ H)) from rfl, hL, hR]
  exact theorem8_1_upperSymmetricGaugeRepulsion_angle A K P Phi hdelta hA hK
    hAP hPlow hPhigh hKP hKPperp

/-- **Theorem 8.1(iii), lower block, in the paper's index order.** -/
theorem theorem8_1_lowerSymmetricGaugeRepulsion_angle_rev
    [FiniteDimensional ℂ H]
    (Phi : FiniteSymmetricGauge (finrank ℂ H))
    (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P) :
    Phi (fun i : Fin (finrank ℂ H) =>
        (lowerBlockShift A P alpha delta).approximationNumber (i.rev : ℕ))
      ≤ Phi (fun i : Fin (finrank ℂ H) =>
        (lowerBlockShift (A + K) (canonicalLowBranch (A + K)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
              (hA.add hK)) alpha) alpha delta).approximationNumber (i.rev : ℕ) *
          TauCeti.principalCosines P (canonicalLowBranch (A + K)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
              (hA.add hK)) alpha) (i.rev : ℕ) ^ 2) := by
  have hL := Phi.perm (fun i : Fin (finrank ℂ H) =>
    (lowerBlockShift A P alpha delta).approximationNumber (i : ℕ))
    (FiniteSymmetricGauge.revPerm (finrank ℂ H))
  have hR := Phi.perm (fun i : Fin (finrank ℂ H) =>
    (lowerBlockShift (A + K) (canonicalLowBranch (A + K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
          (hA.add hK)) alpha) alpha delta).approximationNumber (i : ℕ) *
      TauCeti.principalCosines P (canonicalLowBranch (A + K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
          (hA.add hK)) alpha) (i : ℕ) ^ 2)
    (FiniteSymmetricGauge.revPerm (finrank ℂ H))
  rw [show (fun i : Fin (finrank ℂ H) =>
      (lowerBlockShift A P alpha delta).approximationNumber (i.rev : ℕ)) =
      (fun i : Fin (finrank ℂ H) =>
        (lowerBlockShift A P alpha delta).approximationNumber (i : ℕ)) ∘
        (FiniteSymmetricGauge.revPerm (finrank ℂ H)) from rfl,
    show (fun i : Fin (finrank ℂ H) =>
      (lowerBlockShift (A + K) (canonicalLowBranch (A + K)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
            (hA.add hK)) alpha) alpha delta).approximationNumber (i.rev : ℕ) *
        TauCeti.principalCosines P (canonicalLowBranch (A + K)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
            (hA.add hK)) alpha) (i.rev : ℕ) ^ 2) =
      (fun i : Fin (finrank ℂ H) =>
        (lowerBlockShift (A + K) (canonicalLowBranch (A + K)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
              (hA.add hK)) alpha) alpha delta).approximationNumber (i : ℕ) *
          TauCeti.principalCosines P (canonicalLowBranch (A + K)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
              (hA.add hK)) alpha) (i : ℕ) ^ 2) ∘
        (FiniteSymmetricGauge.revPerm (finrank ℂ H)) from rfl, hL, hR]
  exact theorem8_1_lowerSymmetricGaugeRepulsion_angle A K P Phi hdelta hA hK
    hAP hPlow hPhigh hKP hKPperp

end Source

/-! ### 7. The same six statements over a REAL Hilbert space

`canonicalLowBranch` has no `𝕜`-generic form, so sections 4--6 cannot be
generalized in place.  They can, however, be *restated* over `ℝ` against the
real branch `canonicalLowBranchReal` of `Section8PartIIReal.lean`, and that is
what this section does.  The six statements below are the printed
`cos²θ` vocabulary of Theorem 8.1(ii)--(iii) over `InnerProductSpace ℝ E`.

Nothing here is new mathematics.  Each is exactly its existing real endpoint --
`theorem8_1_{upper,lower}ApproximationRepulsion_real` in
`Section8PartIIReal.lean`, `theorem8_1_{upper,lower}SymmetricGaugeRepulsion_real`
in `Section8PartIIIReal.lean` -- rewritten through the identifications of
sections 1--3, which are `𝕜`-generic and so apply at `ℝ` unchanged.

`[FiniteDimensional ℝ E]` appears on all six, exactly as `[FiniteDimensional ℂ H]`
appears on all six complex ones.  On the symmetric-gauge clauses it is the
paper's own restriction.  On the two part (ii) clauses it is genuinely stronger
than the endpoint being rewritten, which is dimension-free: `principalCosines`
is a finite-dimensional object here, so writing the printed `‖C₁‖₁` as a
principal cosine is precisely where the dimension enters.  The dimension-free
reading of part (ii) over `ℝ` remains available, in the norm form. -/

section SourceReal

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- **Theorem 8.1(ii), upper block, over a REAL Hilbert space, with the printed
factor as a cosine.**

  `α_k - α ≤ cos²θ_max · (λ_k - α)`,

the real sibling of `theorem8_1_upperApproximationRepulsion_angle`: the
printed `α_k - α ≤ ‖C₁‖₁² (λ_k - α)` with `‖C₁‖₁` rewritten as the largest
principal cosine of the pair `(Pᗮ, Qᗮ)`, `Q` the real canonical low branch. -/
theorem theorem8_1_upperApproximationRepulsion_angle_real [FiniteDimensional ℝ E]
    (A K : E →L[ℝ] E) (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P)
    (n : ℕ) :
    (upperBlockShift A P alpha).approximationNumber n ≤
      TauCeti.principalCosines Pᗮ
          (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
            hKPperp)ᗮ 0 ^ 2 *
        (upperBlockShift (A + K)
          (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
            hKPperp) alpha).approximationNumber n := by
  rw [← norm_cosineBlock_eq_principalCosines_zero]
  exact theorem8_1_upperApproximationRepulsion_real A K P hdelta hA hK hAP hPlow
    hPhigh hKP hKPperp n

/-- **Theorem 8.1(ii), lower block, over a REAL Hilbert space, with the printed
factor as a cosine.**  The real sibling of
`theorem8_1_lowerApproximationRepulsion_angle`. -/
theorem theorem8_1_lowerApproximationRepulsion_angle_real [FiniteDimensional ℝ E]
    (A K : E →L[ℝ] E) (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P)
    (n : ℕ) :
    (lowerBlockShift A P alpha delta).approximationNumber n ≤
      TauCeti.principalCosines P
          (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
            hKPperp) 0 ^ 2 *
        (lowerBlockShift (A + K)
          (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
            hKPperp) alpha delta).approximationNumber n := by
  rw [← norm_lowerCosineBlock_eq_principalCosines_zero]
  exact theorem8_1_lowerApproximationRepulsion_real A K P hdelta hA hK hAP hPlow
    hPhigh hKP hKPperp n

/-- **Theorem 8.1(iii), upper block, over a REAL Hilbert space, printed form.**

  `Φ(α₁ - α, …, α_n - α) ≤ Φ((λ₁ - α) cos²θ₁, …, (λ_n - α) cos²θ_n)`

for **every** symmetric gauge `Φ`, with `cos θ_i` the principal cosines of the
pair `(Pᗮ, Qᗮ)`.  Indices run decreasingly; see
`theorem8_1_upperSymmetricGaugeRepulsion_angle_rev_real` for the printed
increasing reading. -/
theorem theorem8_1_upperSymmetricGaugeRepulsion_angle_real [FiniteDimensional ℝ E]
    (Phi : FiniteSymmetricGauge (Module.finrank ℝ E))
    (A K : E →L[ℝ] E) (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P) :
    Phi (fun i : Fin (Module.finrank ℝ E) =>
        (upperBlockShift A P alpha).approximationNumber (i : ℕ))
      ≤ Phi (fun i : Fin (Module.finrank ℝ E) =>
        (upperBlockShift (A + K)
            (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
              hKPperp) alpha).approximationNumber (i : ℕ) *
          TauCeti.principalCosines Pᗮ
            (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
              hKPperp)ᗮ (i : ℕ) ^ 2) := by
  have hrw : (fun i : Fin (Module.finrank ℝ E) =>
      (upperBlockShift (A + K)
          (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
            hKPperp) alpha).approximationNumber (i : ℕ) *
        TauCeti.principalCosines Pᗮ
          (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
            hKPperp)ᗮ (i : ℕ) ^ 2) =
      (fun i : Fin (Module.finrank ℝ E) =>
        (upperBlockShift (A + K)
            (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
              hKPperp) alpha).approximationNumber (i : ℕ) *
          (cosineBlock P
            (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
              hKPperp)).approximationNumber (i : ℕ) ^ 2) := by
    funext i
    rw [approximationNumber_cosineBlock_eq_principalCosines]
  rw [hrw]
  exact theorem8_1_upperSymmetricGaugeRepulsion_real Phi A K P hdelta hA hK hAP
    hPlow hPhigh hKP hKPperp

/-- **Theorem 8.1(iii), lower block, over a REAL Hilbert space, printed form.**
The printed "with a similar relation for `Λ₀`", for every symmetric gauge, with
the principal cosines of `(P, Q)`. -/
theorem theorem8_1_lowerSymmetricGaugeRepulsion_angle_real [FiniteDimensional ℝ E]
    (Phi : FiniteSymmetricGauge (Module.finrank ℝ E))
    (A K : E →L[ℝ] E) (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P) :
    Phi (fun i : Fin (Module.finrank ℝ E) =>
        (lowerBlockShift A P alpha delta).approximationNumber (i : ℕ))
      ≤ Phi (fun i : Fin (Module.finrank ℝ E) =>
        (lowerBlockShift (A + K)
            (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
              hKPperp) alpha delta).approximationNumber (i : ℕ) *
          TauCeti.principalCosines P
            (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
              hKPperp) (i : ℕ) ^ 2) := by
  have hrw : (fun i : Fin (Module.finrank ℝ E) =>
      (lowerBlockShift (A + K)
          (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
            hKPperp) alpha delta).approximationNumber (i : ℕ) *
        TauCeti.principalCosines P
          (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
            hKPperp) (i : ℕ) ^ 2) =
      (fun i : Fin (Module.finrank ℝ E) =>
        (lowerBlockShift (A + K)
            (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
              hKPperp) alpha delta).approximationNumber (i : ℕ) *
          (lowerCosineBlock P
            (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
              hKPperp)).approximationNumber (i : ℕ) ^ 2) := by
    funext i
    rw [approximationNumber_lowerCosineBlock_eq_principalCosines]
  rw [hrw]
  exact theorem8_1_lowerSymmetricGaugeRepulsion_real Phi A K P hdelta hA hK hAP
    hPlow hPhigh hKP hKPperp

/-- **Theorem 8.1(iii), upper block, over a REAL Hilbert space, in the paper's
index order.**  Both sides are reindexed by `Fin.rev` together, so this is a
global reindex and not a reordering of one side against the other; it follows
from the decreasing statement by permutation invariance alone. -/
theorem theorem8_1_upperSymmetricGaugeRepulsion_angle_rev_real
    [FiniteDimensional ℝ E]
    (Phi : FiniteSymmetricGauge (Module.finrank ℝ E))
    (A K : E →L[ℝ] E) (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P) :
    Phi (fun i : Fin (Module.finrank ℝ E) =>
        (upperBlockShift A P alpha).approximationNumber (i.rev : ℕ))
      ≤ Phi (fun i : Fin (Module.finrank ℝ E) =>
        (upperBlockShift (A + K)
            (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
              hKPperp) alpha).approximationNumber (i.rev : ℕ) *
          TauCeti.principalCosines Pᗮ
            (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
              hKPperp)ᗮ (i.rev : ℕ) ^ 2) := by
  have hL := Phi.perm (fun i : Fin (Module.finrank ℝ E) =>
    (upperBlockShift A P alpha).approximationNumber (i : ℕ))
    (FiniteSymmetricGauge.revPerm (Module.finrank ℝ E))
  have hR := Phi.perm (fun i : Fin (Module.finrank ℝ E) =>
    (upperBlockShift (A + K)
        (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
          hKPperp) alpha).approximationNumber (i : ℕ) *
      TauCeti.principalCosines Pᗮ
        (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
          hKPperp)ᗮ (i : ℕ) ^ 2)
    (FiniteSymmetricGauge.revPerm (Module.finrank ℝ E))
  rw [show (fun i : Fin (Module.finrank ℝ E) =>
      (upperBlockShift A P alpha).approximationNumber (i.rev : ℕ)) =
      (fun i : Fin (Module.finrank ℝ E) =>
        (upperBlockShift A P alpha).approximationNumber (i : ℕ)) ∘
        (FiniteSymmetricGauge.revPerm (Module.finrank ℝ E)) from rfl,
    show (fun i : Fin (Module.finrank ℝ E) =>
      (upperBlockShift (A + K)
          (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
            hKPperp) alpha).approximationNumber (i.rev : ℕ) *
        TauCeti.principalCosines Pᗮ
          (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
            hKPperp)ᗮ (i.rev : ℕ) ^ 2) =
      (fun i : Fin (Module.finrank ℝ E) =>
        (upperBlockShift (A + K)
            (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
              hKPperp) alpha).approximationNumber (i : ℕ) *
          TauCeti.principalCosines Pᗮ
            (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
              hKPperp)ᗮ (i : ℕ) ^ 2) ∘
        (FiniteSymmetricGauge.revPerm (Module.finrank ℝ E)) from rfl, hL, hR]
  exact theorem8_1_upperSymmetricGaugeRepulsion_angle_real Phi A K P hdelta hA hK
    hAP hPlow hPhigh hKP hKPperp

/-- **Theorem 8.1(iii), lower block, over a REAL Hilbert space, in the paper's
index order.** -/
theorem theorem8_1_lowerSymmetricGaugeRepulsion_angle_rev_real
    [FiniteDimensional ℝ E]
    (Phi : FiniteSymmetricGauge (Module.finrank ℝ E))
    (A K : E →L[ℝ] E) (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, ⟪A x, x⟫_ℝ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ ⟪A x, x⟫_ℝ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P) :
    Phi (fun i : Fin (Module.finrank ℝ E) =>
        (lowerBlockShift A P alpha delta).approximationNumber (i.rev : ℕ))
      ≤ Phi (fun i : Fin (Module.finrank ℝ E) =>
        (lowerBlockShift (A + K)
            (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
              hKPperp) alpha delta).approximationNumber (i.rev : ℕ) *
          TauCeti.principalCosines P
            (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
              hKPperp) (i.rev : ℕ) ^ 2) := by
  have hL := Phi.perm (fun i : Fin (Module.finrank ℝ E) =>
    (lowerBlockShift A P alpha delta).approximationNumber (i : ℕ))
    (FiniteSymmetricGauge.revPerm (Module.finrank ℝ E))
  have hR := Phi.perm (fun i : Fin (Module.finrank ℝ E) =>
    (lowerBlockShift (A + K)
        (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
          hKPperp) alpha delta).approximationNumber (i : ℕ) *
      TauCeti.principalCosines P
        (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
          hKPperp) (i : ℕ) ^ 2)
    (FiniteSymmetricGauge.revPerm (Module.finrank ℝ E))
  rw [show (fun i : Fin (Module.finrank ℝ E) =>
      (lowerBlockShift A P alpha delta).approximationNumber (i.rev : ℕ)) =
      (fun i : Fin (Module.finrank ℝ E) =>
        (lowerBlockShift A P alpha delta).approximationNumber (i : ℕ)) ∘
        (FiniteSymmetricGauge.revPerm (Module.finrank ℝ E)) from rfl,
    show (fun i : Fin (Module.finrank ℝ E) =>
      (lowerBlockShift (A + K)
          (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
            hKPperp) alpha delta).approximationNumber (i.rev : ℕ) *
        TauCeti.principalCosines P
          (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
            hKPperp) (i.rev : ℕ) ^ 2) =
      (fun i : Fin (Module.finrank ℝ E) =>
        (lowerBlockShift (A + K)
            (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
              hKPperp) alpha delta).approximationNumber (i : ℕ) *
          TauCeti.principalCosines P
            (canonicalLowBranchReal A K P hdelta hA hK hAP hPlow hPhigh hKP
              hKPperp) (i : ℕ) ^ 2) ∘
        (FiniteSymmetricGauge.revPerm (Module.finrank ℝ E)) from rfl, hL, hR]
  exact theorem8_1_lowerSymmetricGaugeRepulsion_angle_real Phi A K P hdelta hA hK
    hAP hPlow hPhigh hKP hKPperp

end SourceReal

/-! ### 8. The section's opening illustration

Section 8 opens by reading a norm bound back as an angle: "if the hypotheses of
the `sin θ` theorem hold with `‖R‖₁ = 1` and `δ = 2`, then `‖sin Θ₀‖₁ ≤ 1/2`,
which is exactly `Θ ≤ π/6`".  The `sin θ` theorem itself is Section 6's; the only
content added there is the scalar dictionary below, the exact analogue of
`maximalAngle_le_pi_div_four_iff` at the sixth of a turn.  Both statements are
`𝕜`-generic: no branch appears in either. -/

section OpeningIllustration

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- `arcsin (1/2) = π/6`. -/
theorem arcsin_one_div_two : Real.arcsin (1 / 2) = Real.pi / 6 :=
  Real.arcsin_eq_of_sin_eq (by rw [Real.sin_pi_div_six])
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

omit [CompleteSpace H] in
/-- **The section's opening reading**: a sine bound of `1/2` is exactly
`Θ ≤ π/6`. -/
theorem maximalAngle_le_pi_div_six_iff (U V : Submodule 𝕜 H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    DavisKahanExt.maximalAngle U V ≤ Real.pi / 6 ↔
      U.projectionGap V ≤ 1 / 2 := by
  have hmem : Real.pi / 6 ∈ Set.Ico (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  show Real.arcsin (U.projectionGap V) ≤ Real.pi / 6 ↔ _
  rw [Real.arcsin_le_iff_le_sin' hmem, Real.sin_pi_div_six]

end OpeningIllustration

end Section8
end DavisKahan1970
end TauCeti
