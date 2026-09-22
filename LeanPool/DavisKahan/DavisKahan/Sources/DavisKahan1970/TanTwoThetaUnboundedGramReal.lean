/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.TanTwoThetaUnboundedGramMiddle
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.UnboundedCompressionReal
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.Complexification.LinearPMapSpectralDescent
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Complexification

/-! # Tan Two Theta Unbounded Gram Real -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# The unbounded `tan 2Θ` endpoint over **real** scalars

`TanTwoThetaUnboundedGramMiddle.lean` proves, over `ℂ`,

`(b - a) · kyFan k (reflectionTangentCorner U Z) ≤ 2 · kyFan k (reflectionResidualCorner U B)`

with `A` unbounded, no extremality hypothesis and no eigenbasis.  This module is
its real sibling.

## Route

The interior of the complex proof runs through `gramSpectralPVM`, whose model
operator is the Cayley transform `1 - (2 i) • resolvent A`; at `RCLike.I = 0`
that formula degenerates rather than generalises, so an in-place `RCLike` edit of
the complex argument is not available.  Instead the *data* is complexified and
the numerical conclusion descended, exactly as in
`DavisKahan/Sources/DavisKahan1970/DirectedUnboundedReal.lean` and
`DavisKahan/Sources/DavisKahan1970/UnboundedCompressionReal.lean`.

The descent is sound because complexification preserves approximation numbers on
the nose, and because every object in the statement is *conjugation fixed*: each
of `Z`, `B`, `A`, `U` and the cutoff net is the complexification of a real
object, so the complex theorem is applied to data that carries no information the
real data did not already have.

## What had to be made scalar generic

Nothing in the statement of the theorem is complex by nature, and the four
carriers were generalised in place rather than duplicated:

* `TauCeti.BoundedCutoff` (`ForTauCeti/Analysis/InnerProductSpace/DoubleAngle/UnboundedPole.lean`);
* `unboundedReflectionTangent` (`TanTwoThetaUnboundedKyFan.lean`);
* `reflectionSineCorner`, `reflectionTangentCorner`, `cutoffCorner` and the block
  compression algebra (`TanTwoThetaUnboundedGramBridge.lean`);
* `reflectionResidualCorner` (`TanTwoThetaUnboundedGramMiddle.lean`).

So the real statement below mentions no complex object at all: `A`, `B`, `Z`,
`U`, the cutoff net and the ideal gauge are all real.

## Main results

* `complexifyBoundedCutoff` — a real bounded cutoff, transported to the
  complexification;
* `approximationSingularValue_blockCompression_complexify` — the exact
  transport of every directed corner's approximation numbers;
* `gap_mul_kyFan_reflectionTangentCorner_le_two_mul_kyFan_real` — the Ky Fan
  prefix endpoint over real scalars;
* `gap_mul_kyFan_reflectionTangentCorner_le_two_mul_kyFan_ambient_real` — the
  same charged to the ambient residual;
* `mem_and_gauge_le_reflectionTangentCorner_real` — the same endpoint at every
  real Fan-dominant unitarily invariant ideal gauge;
* `tanTwoTheta_unbounded_residual_opNorm_real` and
  `tanTwoTheta_unbounded_residual_div_real` — the real counterparts of the
  *pointwise* operator-norm statements of
  `DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedResidual.lean`.

Neither `IsCompressedDoubleAngleEigenbasis` nor any other attainment condition
occurs in the hypotheses or in the transitive constant closure of any of the
three (checked by traversing `ConstantInfo.value? (allowOpaque := true)` from the
three endpoints: 56793 constants, zero hits, while the controls
`gramSpectralPVM`, `GramSpectralBandModel` and `BoundedCutoff` are all present).

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46, Section 7 and the Appendix to
  Section 6.
-/

namespace TauCeti
namespace DavisKahan1970

open scoped InnerProductSpace BigOperators

open TauCeti.ApproximationNumber
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.DavisKahan.ExactSinTheta.ComplexificationApproximation
open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation.RealComplexification
open scoped TauCeti.CompleteSubspace

noncomputable section

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-! ## The reflection blocks under complexification -/

section Blocks

variable (U : Submodule ℝ E) [U.HasOrthogonalProjection]

omit [CompleteSpace E] in
/-- The even reflection block commutes with complexification. -/
theorem diagonalPart_complexifySubmodule (Z : E →L[ℝ] E) :
    (complexifySubmodule U).diagonalPart (complexify Z) =
      complexify (U.diagonalPart Z) := by
  rw [Submodule.diagonalPart_eq, Submodule.diagonalPart_eq,
    starProjection_complexifySubmodule, starProjection_complexifySubmodule_orthogonal,
    complexify_add, complexify_comp, complexify_comp, complexify_comp, complexify_comp]

omit [CompleteSpace E] in
/-- The odd reflection block commutes with complexification. -/
theorem offDiagonalPart_complexifySubmodule (Z : E →L[ℝ] E) :
    (complexifySubmodule U).offDiagonalPart (complexify Z) =
      complexify (U.offDiagonalPart Z) := by
  rw [Submodule.offDiagonalPart_eq, Submodule.offDiagonalPart_eq,
    complexify_sub, diagonalPart_complexifySubmodule]

end Blocks

/-! ## `Ring.inverse` under complexification -/

omit [CompleteSpace E] in
/-- Complexification is a unital ring map, so it carries the `Ring.inverse` of a
unit to the `Ring.inverse` of its image. -/
theorem complexify_ringInverse {T : E →L[ℝ] E} (h : IsUnit T) :
    complexify (Ring.inverse T) = Ring.inverse (complexify T) := by
  have hmul : complexify T * complexify (Ring.inverse T) = 1 := by
    rw [← complexify_mul, Ring.mul_inverse_cancel T h, complexify_one]
  have hmul' : complexify (Ring.inverse T) * complexify T = 1 := by
    rw [← complexify_mul, Ring.inverse_mul_cancel T h, complexify_one]
  let u : (RealComplexification E →L[ℂ] RealComplexification E)ˣ :=
    ⟨complexify T, complexify (Ring.inverse T), hmul, hmul'⟩
  have hcoe : complexify T = (u : RealComplexification E →L[ℂ] RealComplexification E) := rfl
  rw [hcoe, Ring.inverse_unit u]
  rfl

/-! ## The reflection tangent under complexification -/

omit [CompleteSpace E] in
/-- **The unbounded reflection tangent commutes with complexification.**  The
tangent is `S · (C²)⁻¹ · C` in the operator ring, and complexification is a
unital ring map that carries the unit `C²` to the unit `(Cℂ)²`. -/
theorem unboundedReflectionTangent_complexifySubmodule
    (U : Submodule ℝ E) [U.HasOrthogonalProjection] (Z : E →L[ℝ] E)
    (hCC : IsUnit (U.diagonalPart Z * U.diagonalPart Z)) :
    unboundedReflectionTangent (complexifySubmodule U) (complexify Z) =
      complexify (unboundedReflectionTangent U Z) := by
  rw [unboundedReflectionTangent, unboundedReflectionTangent,
    offDiagonalPart_complexifySubmodule, diagonalPart_complexifySubmodule,
    complexify_mul, complexify_mul, complexify_ringInverse hCC, complexify_mul]

/-! ## Exact transport of every directed corner's approximation numbers -/

section Corners

variable (Ω Γ : Submodule ℝ E) [Ω.HasOrthogonalProjection] [Γ.HasOrthogonalProjection]

/-- The block compression, read back into the ambient space, is the pinched
operator.  This is `coe_blockCompression_apply` in operator form. -/
theorem subtypeL_comp_blockCompression (K : E →L[ℝ] E) :
    Ω.subtypeL ∘L blockCompression Ω Γ K =
      Ω.starProjection ∘L K ∘L Γ.subtypeL :=
  ContinuousLinearMap.ext fun z => coe_blockCompression_apply Ω Γ K z

/-- **Through the canonical subspace adapters, the complexified directed corner is
exactly the complexification of the real directed corner.** -/
theorem blockCompression_complexify_equiv (K : E →L[ℝ] E) :
    (complexifySubmoduleEquiv Ω).toContinuousLinearEquiv.toContinuousLinearMap ∘L
        complexify (blockCompression Ω Γ K) ∘L
        (complexifySubmoduleEquiv Γ).symm.toContinuousLinearEquiv.toContinuousLinearMap =
      blockCompression (complexifySubmodule Ω) (complexifySubmodule Γ)
        (complexify K) := by
  refine ContinuousLinearMap.ext fun y => Subtype.ext ?_
  set w := (complexifySubmoduleEquiv Γ).symm y with hwdef
  have hy : complexifySubmoduleEquiv Γ w = y :=
    (complexifySubmoduleEquiv Γ).apply_symm_apply y
  have hycoe : ((y : complexifySubmodule Γ) : RealComplexification E) =
      complexify Γ.subtypeL w := by
    rw [← hy]
    exact coe_complexifySubmoduleEquiv_eq_complexify_subtypeL Γ w
  have hlhs :
      ((((complexifySubmoduleEquiv Ω).toContinuousLinearEquiv.toContinuousLinearMap ∘L
          complexify (blockCompression Ω Γ K) ∘L
          (complexifySubmoduleEquiv Γ).symm.toContinuousLinearEquiv.toContinuousLinearMap)
            y : complexifySubmodule Ω) : RealComplexification E) =
        complexify (Ω.subtypeL ∘L blockCompression Ω Γ K) w := by
    rw [complexify_comp]
    exact coe_complexifySubmoduleEquiv_eq_complexify_subtypeL Ω
      (complexify (blockCompression Ω Γ K) w)
  rw [hlhs, subtypeL_comp_blockCompression,
    coe_blockCompression_apply, starProjection_complexifySubmodule, hycoe,
    complexify_comp, complexify_comp]
  rfl

/-- **Approximation singular values of a directed corner are preserved on the nose
by complexification.**  This is what makes the descent of the `tan 2Θ` endpoint
sound. -/
theorem approximationSingularValue_blockCompression_complexify
    (K : E →L[ℝ] E) (n : ℕ) :
    approximationSingularValue n
        (blockCompression (complexifySubmodule Ω) (complexifySubmodule Γ)
          (complexify K)) =
      approximationSingularValue n (blockCompression Ω Γ K) := by
  have hsame := SameApproximationSingularValues.of_isometricEquiv_comp
    (complexifySubmoduleEquiv Ω) (complexifySubmoduleEquiv Γ)
    (blockCompression_complexify_equiv Ω Γ K)
  exact (hsame n).symm.trans
    (approximationSingularValue_complexify (blockCompression Ω Γ K) n)

/-- The finite Ky Fan gauge of a directed corner is preserved on the nose by
complexification. -/
theorem kyFanApproximationGauge_blockCompression_complexify
    (K : E →L[ℝ] E) (k : ℕ) :
    kyFanApproximationGauge k
        (blockCompression (complexifySubmodule Ω) (complexifySubmodule Γ)
          (complexify K)) =
      kyFanApproximationGauge k (blockCompression Ω Γ K) := by
  unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
  exact Finset.sum_congr rfl fun n _ =>
    approximationSingularValue_blockCompression_complexify Ω Γ K n

end Corners

/-! ## A real bounded cutoff, transported to the complexification -/

section Cutoff

variable {A : E →ₗ.[ℝ] E} {U : Submodule ℝ E} [U.HasOrthogonalProjection] {τ : ℝ}

/-- **The complexification of a real bounded low-energy cutoff.**

Every field is coordinatewise: the projection is `complexify Ω.toProj`, and each
of the six conditions is the pair of real conditions on the two coordinates.
The only inequality that is not immediate is the form bound, where the two
coordinate bounds are combined through `‖z‖² = ‖re z‖² + ‖im z‖²`. -/
def complexifyBoundedCutoff (Ω : TauCeti.BoundedCutoff A U τ) :
    TauCeti.BoundedCutoff (TauCeti.LinearPMap.complexifyReal A)
      (complexifySubmodule U) τ where
  toProj := complexify Ω.toProj
  isSelfAdjoint := (complexify_isSelfAdjoint_iff Ω.toProj).2 Ω.isSelfAdjoint
  isIdempotentElem := by
    change complexify Ω.toProj * complexify Ω.toProj = complexify Ω.toProj
    rw [← complexify_mul, Ω.isIdempotentElem.eq]
  mem_subspace := fun v => by
    rw [mem_complexifySubmodule, re_complexify, im_complexify]
    exact ⟨Ω.mem_subspace _, Ω.mem_subspace _⟩
  mem_domain := fun v => by
    rw [TauCeti.LinearPMap.mem_complexifyReal_domain_iff, re_complexify, im_complexify]
    exact ⟨Ω.mem_domain _, Ω.mem_domain _⟩
  norm_apply_le := fun v => by
    have hdre : Ω.toProj (re v) ∈ A.domain := Ω.mem_domain (re v)
    have hdim : Ω.toProj (im v) ∈ A.domain := Ω.mem_domain (im v)
    set w : RealComplexification E := complexify Ω.toProj v with hwdef
    have hre : re w = Ω.toProj (re v) := re_complexify Ω.toProj v
    have him : im w = Ω.toProj (im v) := im_complexify Ω.toProj v
    have hmem : w ∈ (TauCeti.LinearPMap.complexifyReal A).domain := by
      rw [TauCeti.LinearPMap.mem_complexifyReal_domain_iff, hre, him]
      exact ⟨hdre, hdim⟩
    have ere : re (TauCeti.LinearPMap.complexifyReal A ⟨w, hmem⟩) =
        A ⟨Ω.toProj (re v), hdre⟩ := by
      rw [TauCeti.LinearPMap.complexifyReal_apply_re]
      exact congrArg A (Subtype.ext hre)
    have eim : im (TauCeti.LinearPMap.complexifyReal A ⟨w, hmem⟩) =
        A ⟨Ω.toProj (im v), hdim⟩ := by
      rw [TauCeti.LinearPMap.complexifyReal_apply_im]
      exact congrArg A (Subtype.ext him)
    have hsplit : ‖TauCeti.LinearPMap.complexifyReal A ⟨w, hmem⟩‖ ^ 2 =
        ‖A ⟨Ω.toProj (re v), hdre⟩‖ ^ 2 + ‖A ⟨Ω.toProj (im v), hdim⟩‖ ^ 2 := by
      rw [RealComplexification.norm_sq, ere, eim]
    have hwsq : ‖w‖ ^ 2 = ‖Ω.toProj (re v)‖ ^ 2 + ‖Ω.toProj (im v)‖ ^ 2 := by
      rw [RealComplexification.norm_sq, hre, him]
    have h1 : ‖A ⟨Ω.toProj (re v), hdre⟩‖ ≤ τ * ‖Ω.toProj (re v)‖ :=
      Ω.norm_apply_le (re v)
    have h2 : ‖A ⟨Ω.toProj (im v), hdim⟩‖ ≤ τ * ‖Ω.toProj (im v)‖ :=
      Ω.norm_apply_le (im v)
    rcases le_or_gt 0 τ with hτ | hτ
    · have s1 : ‖A ⟨Ω.toProj (re v), hdre⟩‖ ^ 2 ≤ τ ^ 2 * ‖Ω.toProj (re v)‖ ^ 2 := by
        have := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hτ (norm_nonneg _))).2 h1
        rwa [mul_pow] at this
      have s2 : ‖A ⟨Ω.toProj (im v), hdim⟩‖ ^ 2 ≤ τ ^ 2 * ‖Ω.toProj (im v)‖ ^ 2 := by
        have := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hτ (norm_nonneg _))).2 h2
        rwa [mul_pow] at this
      rw [← sq_le_sq₀ (norm_nonneg _) (mul_nonneg hτ (norm_nonneg _)), mul_pow, hsplit,
        hwsq, mul_add]
      linarith
    · have hzre : Ω.toProj (re v) = 0 := by
        by_contra hne
        have hpos : 0 < ‖Ω.toProj (re v)‖ := norm_pos_iff.2 hne
        nlinarith [h1, norm_nonneg (A ⟨Ω.toProj (re v), hdre⟩)]
      have hzim : Ω.toProj (im v) = 0 := by
        by_contra hne
        have hpos : 0 < ‖Ω.toProj (im v)‖ := norm_pos_iff.2 hne
        nlinarith [h2, norm_nonneg (A ⟨Ω.toProj (im v), hdim⟩)]
      have hw0 : w = 0 := by
        have hsq : ‖w‖ ^ 2 = 0 := by rw [hwsq, hzre, hzim]; simp
        have hn : ‖w‖ = 0 := by nlinarith [norm_nonneg w]
        exact norm_eq_zero.mp hn
      have hdomzero : (⟨w, hmem⟩ : (TauCeti.LinearPMap.complexifyReal A).domain) = 0 :=
        Subtype.ext hw0
      rw [hdomzero, (TauCeti.LinearPMap.complexifyReal A).map_zero, ← hwdef, hw0]
      simp
  apply_mem_range := fun v => by
    refine RealComplexification.ext ?_ ?_
    · rw [re_complexify]
      exact Ω.apply_mem_range (re v)
    · rw [im_complexify]
      exact Ω.apply_mem_range (im v)

/-- Through the canonical subspace adapter, the compressed complexified cutoff is
the complexification of the compressed real cutoff. -/
theorem cutoffCorner_complexifyBoundedCutoff (Ω : TauCeti.BoundedCutoff A U τ) :
    (complexifySubmoduleEquiv U).toContinuousLinearEquiv.toContinuousLinearMap ∘L
        complexify (cutoffCorner Ω) ∘L
        (complexifySubmoduleEquiv U).symm.toContinuousLinearEquiv.toContinuousLinearMap =
      cutoffCorner (complexifyBoundedCutoff Ω) := by
  rw [cutoffCorner, cutoffCorner]
  exact blockCompression_complexify_equiv U U Ω.toProj

end Cutoff

/-! ## Strong convergence under complexification -/

/-- Strong operator convergence is preserved by complexification: the two
coordinates converge separately and `‖z‖ ≤ ‖re z‖ + ‖im z‖`. -/
theorem stronglyTendsto_complexify {ι : Type*} {l : Filter ι}
    {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℝ F] 
    {T : ι → F →L[ℝ] F} {S : F →L[ℝ] F}
    (h : TauCeti.ApproximationNumber.StronglyTendsto T l S) :
    TauCeti.ApproximationNumber.StronglyTendsto (fun i => complexify (T i)) l
      (complexify S) := by
  intro u
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hre := h (re u)
  have him := h (im u)
  rw [tendsto_iff_norm_sub_tendsto_zero] at hre him
  refine squeeze_zero (fun i => norm_nonneg _) (fun i => ?_)
    (by simpa using hre.add him)
  have e1 : re (complexify (T i) u - complexify S u) = T i (re u) - S (re u) := by
    rw [re_sub, re_complexify, re_complexify]
  have e2 : im (complexify (T i) u - complexify S u) = T i (im u) - S (im u) := by
    rw [im_sub, im_complexify, im_complexify]
  have hsq : ‖complexify (T i) u - complexify S u‖ ^ 2 =
      ‖T i (re u) - S (re u)‖ ^ 2 + ‖T i (im u) - S (im u)‖ ^ 2 := by
    rw [RealComplexification.norm_sq, e1, e2]
  nlinarith [hsq, norm_nonneg (complexify (T i) u - complexify S u),
    norm_nonneg (T i (re u) - S (re u)), norm_nonneg (T i (im u) - S (im u)),
    mul_nonneg (norm_nonneg (T i (re u) - S (re u)))
      (norm_nonneg (T i (im u) - S (im u)))]

/-! ## Transport of the printed hypotheses -/

section Hypotheses

variable {A : E →ₗ.[ℝ] E} {U : Submodule ℝ E} [U.HasOrthogonalProjection]
  {B Z : E →L[ℝ] E}

omit [CompleteSpace E] [U.HasOrthogonalProjection] in
/-- Oddness for the splitting is preserved by complexification. -/
theorem isOddFor_complexifySubmodule (hB : TauCeti.IsOddFor U B) :
    TauCeti.IsOddFor (complexifySubmodule U) (complexify B) := by
  constructor
  · intro z hz
    rw [mem_complexifySubmodule] at hz
    rw [← complexifySubmodule_orthogonal, mem_complexifySubmodule, re_complexify,
      im_complexify]
    exact ⟨hB.1 _ hz.1, hB.1 _ hz.2⟩
  · intro z hz
    rw [← complexifySubmodule_orthogonal, mem_complexifySubmodule] at hz
    rw [mem_complexifySubmodule, re_complexify, im_complexify]
    exact ⟨hB.2 _ hz.1, hB.2 _ hz.2⟩

omit [CompleteSpace E] in
/-- The reducing-subspace property is preserved by complexification. -/
theorem reducesSubspace_complexifyReal
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) :
    TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.complexifyReal A)
      (complexifySubmodule U) := by
  refine TauCeti.LinearPMap.ReducesSubspace.of_components ?_ ?_ ?_ ?_
  · intro x
    rw [starProjection_complexifySubmodule,
      TauCeti.LinearPMap.mem_complexifyReal_domain_iff, re_complexify, im_complexify]
    exact ⟨hred.projection_mem_domain (TauCeti.LinearPMap.complexificationDomainRe A x),
      hred.projection_mem_domain (TauCeti.LinearPMap.complexificationDomainIm A x)⟩
  · intro x
    rw [starProjection_complexifySubmodule_orthogonal,
      TauCeti.LinearPMap.mem_complexifyReal_domain_iff, re_complexify, im_complexify]
    exact ⟨hred.orthogonalProjection_mem_domain
        (TauCeti.LinearPMap.complexificationDomainRe A x),
      hred.orthogonalProjection_mem_domain
        (TauCeti.LinearPMap.complexificationDomainIm A x)⟩
  · intro x hx
    rw [mem_complexifySubmodule] at hx
    rw [mem_complexifySubmodule, TauCeti.LinearPMap.complexifyReal_apply_re,
      TauCeti.LinearPMap.complexifyReal_apply_im]
    exact ⟨hred.invariant _ hx.1, hred.invariant _ hx.2⟩
  · intro x hx
    rw [← complexifySubmodule_orthogonal, mem_complexifySubmodule] at hx
    rw [← complexifySubmodule_orthogonal, mem_complexifySubmodule,
      TauCeti.LinearPMap.complexifyReal_apply_re,
      TauCeti.LinearPMap.complexifyReal_apply_im]
    exact ⟨hred.orthogonal_invariant _ hx.1, hred.orthogonal_invariant _ hx.2⟩

omit [CompleteSpace E] in
/-- Domain transport is preserved by complexification. -/
theorem mapsDomainTo_complexifyReal
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z) :
    TauCeti.LinearPMap.MapsDomainTo (TauCeti.LinearPMap.complexifyReal A)
      (TauCeti.LinearPMap.complexifyReal A) (complexify Z) := by
  intro x
  rw [TauCeti.LinearPMap.mem_complexifyReal_domain_iff, re_complexify, im_complexify]
  exact ⟨hZdom (TauCeti.LinearPMap.complexificationDomainRe A x),
    hZdom (TauCeti.LinearPMap.complexificationDomainIm A x)⟩


omit [CompleteSpace E] [U.HasOrthogonalProjection] in
/-- **Complexification commutes with a bounded perturbation of a partial map.**
`A + B` has `A`'s domain and acts coordinatewise, and so does its
complexification, so the two ways of forming `(A + B)_ℂ` agree on the nose. -/
theorem complexifyReal_addBounded (A : E →ₗ.[ℝ] E) (B : E →L[ℝ] E) :
    TauCeti.LinearPMap.complexifyReal (TauCeti.LinearPMap.addBounded A B) =
      TauCeti.LinearPMap.addBounded (TauCeti.LinearPMap.complexifyReal A) (complexify B) := by
  refine _root_.LinearPMap.ext rfl ?_
  intro z hf hg
  refine RealComplexification.ext ?_ ?_
  · change A ⟨re z, hg.1⟩ + B (re z) = A ⟨re z, hg.1⟩ + re (complexify B z)
    rw [re_complexify]
  · change A ⟨im z, hg.2⟩ + B (im z) = A ⟨im z, hg.2⟩ + im (complexify B z)
    rw [im_complexify]

omit [CompleteSpace E] in
/-- **A subspace reducing `A + B` complexifies to one reducing `A_ℂ + B_ℂ`.**
This is the transport of the paper's "`V` reduces `A + H`" hypothesis. -/
theorem reducesSubspace_addBounded_complexifyReal
    {V : Submodule ℝ E} [V.HasOrthogonalProjection]
    (hV : TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.addBounded A B) V) :
    TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded (TauCeti.LinearPMap.complexifyReal A) (complexify B))
      (complexifySubmodule V) := by
  rw [← complexifyReal_addBounded]
  exact reducesSubspace_complexifyReal hV

omit [CompleteSpace E] [U.HasOrthogonalProjection] in
/-- **An upper form bound on a subspace transports to its complexification with
the same constant.**  The real part of the complexified form is the sum of the
real form on the real and imaginary coordinates. -/
theorem re_inner_complexifyReal_le_of_forall_mem {a : ℝ}
    (hUa : ∀ x : A.domain, (x : E) ∈ U → ⟪A x, (x : E)⟫_ℝ ≤ a * ‖(x : E)‖ ^ 2) :
    ∀ y : (TauCeti.LinearPMap.complexifyReal A).domain,
      (y : RealComplexification E) ∈ complexifySubmodule U →
      RCLike.re ⟪TauCeti.LinearPMap.complexifyReal A y, (y : RealComplexification E)⟫_ℂ ≤
        a * ‖(y : RealComplexification E)‖ ^ 2 := by
  intro y hy
  rw [mem_complexifySubmodule] at hy
  have hcoord := (TauCeti.LinearPMap.mem_complexifyReal_domain_iff A
    (y : RealComplexification E)).mp y.2
  have h1 := hUa ⟨re (y : RealComplexification E), hcoord.1⟩ hy.1
  have h2 := hUa ⟨im (y : RealComplexification E), hcoord.2⟩ hy.2
  have hsplit : RCLike.re ⟪TauCeti.LinearPMap.complexifyReal A y,
        (y : RealComplexification E)⟫_ℂ =
      ⟪A ⟨re (y : RealComplexification E), hcoord.1⟩,
          re (y : RealComplexification E)⟫_ℝ +
        ⟪A ⟨im (y : RealComplexification E), hcoord.2⟩,
          im (y : RealComplexification E)⟫_ℝ := rfl
  rw [hsplit, RealComplexification.norm_sq, mul_add]
  linarith

omit [CompleteSpace E] [U.HasOrthogonalProjection] in
/-- **A lower form bound on the orthogonal complement transports to the
complexification with the same constant.** -/
theorem le_re_inner_complexifyReal_of_forall_mem_orthogonal {b : ℝ}
    (hUb : ∀ x : A.domain, (x : E) ∈ Uᗮ → b * ‖(x : E)‖ ^ 2 ≤ ⟪A x, (x : E)⟫_ℝ) :
    ∀ y : (TauCeti.LinearPMap.complexifyReal A).domain,
      (y : RealComplexification E) ∈ (complexifySubmodule U)ᗮ →
      b * ‖(y : RealComplexification E)‖ ^ 2 ≤
        RCLike.re ⟪TauCeti.LinearPMap.complexifyReal A y, (y : RealComplexification E)⟫_ℂ := by
  intro y hy
  rw [← complexifySubmodule_orthogonal, mem_complexifySubmodule] at hy
  have hcoord := (TauCeti.LinearPMap.mem_complexifyReal_domain_iff A
    (y : RealComplexification E)).mp y.2
  have h1 := hUb ⟨re (y : RealComplexification E), hcoord.1⟩ hy.1
  have h2 := hUb ⟨im (y : RealComplexification E), hcoord.2⟩ hy.2
  have hsplit : RCLike.re ⟪TauCeti.LinearPMap.complexifyReal A y,
        (y : RealComplexification E)⟫_ℂ =
      ⟪A ⟨re (y : RealComplexification E), hcoord.1⟩,
          re (y : RealComplexification E)⟫_ℝ +
        ⟪A ⟨im (y : RealComplexification E), hcoord.2⟩,
          im (y : RealComplexification E)⟫_ℝ := rfl
  rw [hsplit, RealComplexification.norm_sq, mul_add]
  linarith

end Hypotheses

/-! ## The directed corner gauge, transported without a subtype cast

`(complexifySubmodule U)ᗮ` and `complexifySubmodule Uᗮ` are equal submodules but
not syntactically equal, and they occur in the *type* of a directed corner.  The
transport therefore runs through the *ambient* projection block
`projectionBlock`, which has type `Eℂ →L[ℂ] Eℂ` and so carries no subtype at
all; `projectionBlock_same_compression` returns to the typed corner at each
end. -/

section CornerGauge

variable (U : Submodule ℝ E) [U.HasOrthogonalProjection]

omit [CompleteSpace E] in
/-- The ambient directed projection block commutes with complexification.

TODO(dedupe): `AmbientReal.projectionBlock_complexifySubmodule_real` states the same
equality with the same proof; neither module imports the other.  One should go. -/
theorem projectionBlock_complexifySubmodule (K : E →L[ℝ] E) :
    projectionBlock (complexifySubmodule U)ᗮ (complexifySubmodule U)
        (complexify K) =
      complexify (projectionBlock Uᗮ U K) := by
  rw [projectionBlock, projectionBlock,
    starProjection_complexifySubmodule_orthogonal, starProjection_complexifySubmodule,
    complexify_comp, complexify_comp]

/-- **The Ky Fan gauge of a directed corner is preserved on the nose by
complexification.**  This is the single numerical fact the descent needs. -/
theorem kyFanApproximationGauge_directedCorner_complexify (K : E →L[ℝ] E) (k : ℕ) :
    kyFanApproximationGauge k
        (blockCompression (complexifySubmodule U)ᗮ (complexifySubmodule U)
          (complexify K)) =
      kyFanApproximationGauge k (blockCompression Uᗮ U K) := by
  have hc := (projectionBlock_same_compression (complexifySubmodule U)ᗮ
    (complexifySubmodule U) (complexify K)).symm.kyFanApproximationGauge_eq k
  have hr := (projectionBlock_same_compression Uᗮ U K).kyFanApproximationGauge_eq k
  rw [hc, projectionBlock_complexifySubmodule,
    kyFanApproximationGauge_complexify, hr]

end CornerGauge

/-! ## The real endpoints -/

section Endpoints

variable {A : E →ₗ.[ℝ] E} {U : Submodule ℝ E} [U.HasOrthogonalProjection]
  {B Z : E →L[ℝ] E} {a b : ℝ}

/-- **The unbounded, residual-form `tan 2Θ` theorem at every Ky Fan prefix, over
real scalars, with no extremality hypothesis.**

`δ · kyFan k T₀ ≤ 2 · kyFan k R₀` on the typed directed corners of a *real*
Hilbert space.  Every object is real: the ambient space, the unbounded operator
`A`, the odd perturbation `B`, the involution `Z`, the trial subspace `U` and the
cutoff net.

Neither this endpoint nor its complex sibling
`gap_mul_kyFan_reflectionTangentCorner_le_two_mul_kyFan` asks for the compressed
cutoffs to be orthogonal projections: `isOrthogonalProjectionMap_cutoffCorner`
proves that unconditionally for every `BoundedCutoff`. -/
theorem gap_mul_kyFan_reflectionTangentCorner_le_two_mul_kyFan_real
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : E), hZdom x⟩ + B (Z (x : E)) = Z (A x) + Z (B (x : E)))
    (hUa : ∀ x : A.domain, (x : E) ∈ U → ⟪A x, (x : E)⟫_ℝ ≤ a * ‖(x : E)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : E) ∈ Uᗮ → b * ‖(x : E)‖ ^ 2 ≤ ⟪A x, (x : E)⟫_ℝ)
    (hab : a < b) (hS1 : ‖U.offDiagonalPart Z‖ < 1)
    {ι : Type*} {l : Filter ι} [l.NeBot] {σ : ι → ℝ} (hσ : ∀ i, 0 ≤ σ i)
    (Ω : ∀ i, TauCeti.BoundedCutoff A U (σ i))
    (hstrong : TauCeti.ApproximationNumber.StronglyTendsto
      (fun i => cutoffCorner (Ω i)) l (ContinuousLinearMap.id ℝ U))
    (k : ℕ) :
    (b - a) * kyFanApproximationGauge k (reflectionTangentCorner U Z) ≤
      2 * kyFanApproximationGauge k (reflectionResidualCorner U B) := by
  classical
  -- the pole is excluded over `ℝ` exactly as it is over `ℂ`
  have hSS : ‖U.offDiagonalPart Z * U.offDiagonalPart Z‖ < 1 := by
    have hle : ‖U.offDiagonalPart Z * U.offDiagonalPart Z‖ ≤
        ‖U.offDiagonalPart Z‖ * ‖U.offDiagonalPart Z‖ := norm_mul_le _ _
    nlinarith [norm_nonneg (U.offDiagonalPart Z)]
  have hCC : IsUnit (U.diagonalPart Z * U.diagonalPart Z) := by
    have hsum := TauCeti.diagonalPart_sq_add_offDiagonalPart_sq (U := U) hZ2
    have hCCeq : U.diagonalPart Z * U.diagonalPart Z =
        1 - U.offDiagonalPart Z * U.offDiagonalPart Z := by
      rw [← hsum]; abel
    rw [hCCeq]
    exact ⟨Units.oneSub _ hSS, rfl⟩
  -- the transported hypotheses
  have hZdom' := mapsDomainTo_complexifyReal hZdom
  have hZcomm' : ∀ x : (TauCeti.LinearPMap.complexifyReal A).domain,
      TauCeti.LinearPMap.complexifyReal A
          ⟨complexify Z (x : RealComplexification E), hZdom' x⟩ +
        complexify B (complexify Z (x : RealComplexification E)) =
      complexify Z (TauCeti.LinearPMap.complexifyReal A x) +
        complexify Z (complexify B (x : RealComplexification E)) := by
    intro x
    have hcoord := (TauCeti.LinearPMap.mem_complexifyReal_domain_iff A
      (x : RealComplexification E)).mp x.2
    refine RealComplexification.ext ?_ ?_
    · exact hZcomm ⟨re (x : RealComplexification E), hcoord.1⟩
    · exact hZcomm ⟨im (x : RealComplexification E), hcoord.2⟩
  have hUa' : ∀ x : (TauCeti.LinearPMap.complexifyReal A).domain,
      (x : RealComplexification E) ∈ complexifySubmodule U →
      RCLike.re ⟪TauCeti.LinearPMap.complexifyReal A x,
          (x : RealComplexification E)⟫_ℂ ≤
        a * ‖(x : RealComplexification E)‖ ^ 2 := by
    intro x hx
    rw [mem_complexifySubmodule] at hx
    have hcoord := (TauCeti.LinearPMap.mem_complexifyReal_domain_iff A
      (x : RealComplexification E)).mp x.2
    have h1 := hUa ⟨re (x : RealComplexification E), hcoord.1⟩ hx.1
    have h2 := hUa ⟨im (x : RealComplexification E), hcoord.2⟩ hx.2
    have hsplit : RCLike.re ⟪TauCeti.LinearPMap.complexifyReal A x,
          (x : RealComplexification E)⟫_ℂ =
        ⟪A ⟨re (x : RealComplexification E), hcoord.1⟩,
            re (x : RealComplexification E)⟫_ℝ +
          ⟪A ⟨im (x : RealComplexification E), hcoord.2⟩,
            im (x : RealComplexification E)⟫_ℝ := rfl
    rw [hsplit, RealComplexification.norm_sq, mul_add]
    linarith
  have hUb' : ∀ x : (TauCeti.LinearPMap.complexifyReal A).domain,
      (x : RealComplexification E) ∈ (complexifySubmodule U)ᗮ →
      b * ‖(x : RealComplexification E)‖ ^ 2 ≤
        RCLike.re ⟪TauCeti.LinearPMap.complexifyReal A x,
          (x : RealComplexification E)⟫_ℂ := by
    intro x hx
    rw [← complexifySubmodule_orthogonal, mem_complexifySubmodule] at hx
    have hcoord := (TauCeti.LinearPMap.mem_complexifyReal_domain_iff A
      (x : RealComplexification E)).mp x.2
    have h1 := hUb ⟨re (x : RealComplexification E), hcoord.1⟩ hx.1
    have h2 := hUb ⟨im (x : RealComplexification E), hcoord.2⟩ hx.2
    have hsplit : RCLike.re ⟪TauCeti.LinearPMap.complexifyReal A x,
          (x : RealComplexification E)⟫_ℂ =
        ⟪A ⟨re (x : RealComplexification E), hcoord.1⟩,
            re (x : RealComplexification E)⟫_ℝ +
          ⟪A ⟨im (x : RealComplexification E), hcoord.2⟩,
            im (x : RealComplexification E)⟫_ℝ := rfl
    rw [hsplit, RealComplexification.norm_sq, mul_add]
    linarith
  have hS1' : ‖(complexifySubmodule U).offDiagonalPart (complexify Z)‖ < 1 := by
    rw [offDiagonalPart_complexifySubmodule, norm_complexify]
    exact hS1
  have hstrong' : TauCeti.ApproximationNumber.StronglyTendsto
      (fun i => cutoffCorner (complexifyBoundedCutoff (Ω i))) l
      (ContinuousLinearMap.id ℂ (complexifySubmodule U)) := by
    intro z
    have hbase := stronglyTendsto_complexify hstrong ((complexifySubmoduleEquiv U).symm z)
    rw [complexify_id] at hbase
    have hcont := ((complexifySubmoduleEquiv U).continuous.continuousAt
      (x := (complexifySubmoduleEquiv U).symm z)).tendsto.comp hbase
    rw [(complexifySubmoduleEquiv U).apply_symm_apply z] at hcont
    refine hcont.congr fun i => ?_
    have h := congrArg (fun T => T z) (cutoffCorner_complexifyBoundedCutoff (Ω i))
    exact h
  -- the complex endpoint, applied to the complexified data
  have hcomplex := gap_mul_kyFan_reflectionTangentCorner_le_two_mul_kyFan
    (A := TauCeti.LinearPMap.complexifyReal A) (U := complexifySubmodule U)
    (B := complexify B) (Z := complexify Z) (a := a) (b := b)
    (reducesSubspace_complexifyReal hred) (isOddFor_complexifySubmodule hB)
    ((complexify_isSelfAdjoint_iff Z).2 hZsa)
    (by rw [← complexify_mul, hZ2, complexify_one])
    hZdom' hZcomm' hUa' hUb' hab hS1' hσ
    (fun i => complexifyBoundedCutoff (Ω i)) hstrong' k
  -- and the descent
  have htan : reflectionTangentCorner (complexifySubmodule U) (complexify Z) =
      blockCompression (complexifySubmodule U)ᗮ (complexifySubmodule U)
        (complexify (unboundedReflectionTangent U Z)) := by
    unfold reflectionTangentCorner
    rw [unboundedReflectionTangent_complexifySubmodule U Z hCC]
  have hres : reflectionResidualCorner (complexifySubmodule U) (complexify B) =
      blockCompression (complexifySubmodule U)ᗮ (complexifySubmodule U)
        (complexify B) := rfl
  rw [htan, hres, kyFanApproximationGauge_directedCorner_complexify U
      (unboundedReflectionTangent U Z) k,
    kyFanApproximationGauge_directedCorner_complexify U B k] at hcomplex
  exact hcomplex

/-- **The real endpoint against the ambient residual.**  The form the exact- and
compressed-eigenfamily endpoints are stated in, now over real scalars and with no
extremality hypothesis. -/
theorem gap_mul_kyFan_reflectionTangentCorner_le_two_mul_kyFan_ambient_real
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : E), hZdom x⟩ + B (Z (x : E)) = Z (A x) + Z (B (x : E)))
    (hUa : ∀ x : A.domain, (x : E) ∈ U → ⟪A x, (x : E)⟫_ℝ ≤ a * ‖(x : E)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : E) ∈ Uᗮ → b * ‖(x : E)‖ ^ 2 ≤ ⟪A x, (x : E)⟫_ℝ)
    (hab : a < b) (hS1 : ‖U.offDiagonalPart Z‖ < 1)
    {ι : Type*} {l : Filter ι} [l.NeBot] {σ : ι → ℝ} (hσ : ∀ i, 0 ≤ σ i)
    (Ω : ∀ i, TauCeti.BoundedCutoff A U (σ i))
    (hstrong : TauCeti.ApproximationNumber.StronglyTendsto
      (fun i => cutoffCorner (Ω i)) l (ContinuousLinearMap.id ℝ U))
    (k : ℕ) :
    (b - a) * kyFanApproximationGauge k (reflectionTangentCorner U Z) ≤
      2 * kyFanApproximationGauge k B := by
  have h := gap_mul_kyFan_reflectionTangentCorner_le_two_mul_kyFan_real hred hB hZsa
    hZ2 hZdom hZcomm hUa hUb hab hS1 hσ Ω hstrong k
  have h2 := kyFanApproximationGauge_reflectionResidualCorner_le U B k
  linarith

/-- **The unbounded, residual-form `tan 2Θ` theorem at every *real* Fan-dominant
unitarily invariant ideal gauge, with no extremality hypothesis.**

`δ N(tan 2Θ₀) ≤ 2 N(R₀)` in the repository's scaled form, on the typed directed
corners of a real Hilbert space.  Ideal membership of the scaled tangent corner is
concluded, not assumed.

This is the real sibling of `mem_and_gauge_le_reflectionTangentCorner`: the
arbitrary-unitarily-invariant-norm endpoint of the unbounded `tan 2Θ` chain, with
`IsCompressedDoubleAngleEigenbasis` deleted rather than discharged, over real
scalars. -/
theorem mem_and_gauge_le_reflectionTangentCorner_real
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (hred : TauCeti.LinearPMap.ReducesSubspace A U) (hB : TauCeti.IsOddFor U B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : E), hZdom x⟩ + B (Z (x : E)) = Z (A x) + Z (B (x : E)))
    (hUa : ∀ x : A.domain, (x : E) ∈ U → ⟪A x, (x : E)⟫_ℝ ≤ a * ‖(x : E)‖ ^ 2)
    (hUb : ∀ x : A.domain, (x : E) ∈ Uᗮ → b * ‖(x : E)‖ ^ 2 ≤ ⟪A x, (x : E)⟫_ℝ)
    (hab : a < b) (hS1 : ‖U.offDiagonalPart Z‖ < 1)
    {ι : Type*} {l : Filter ι} [l.NeBot] {σ : ι → ℝ} (hσ : ∀ i, 0 ≤ σ i)
    (Ω : ∀ i, TauCeti.BoundedCutoff A U (σ i))
    (hstrong : TauCeti.ApproximationNumber.StronglyTendsto
      (fun i => cutoffCorner (Ω i)) l (ContinuousLinearMap.id ℝ U))
    (hBmem : N.Mem (reflectionResidualCorner U B)) :
    N.Mem (((b - a) / 2 : ℝ) • reflectionTangentCorner U Z) ∧
      N.gauge (((b - a) / 2 : ℝ) • reflectionTangentCorner U Z) ≤
        N.gauge (reflectionResidualCorner U B) := by
  refine mem_and_gauge_le_of_all_kyFanApproximationGauge_le N.toFanDominantIdealFamily hBmem fun k => ?_
  rw [kyFanApproximationGauge_smul, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ (b - a) / 2)]
  have h := gap_mul_kyFan_reflectionTangentCorner_le_two_mul_kyFan_real hred hB hZsa
    hZ2 hZdom hZcomm hUa hUb hab hS1 hσ Ω hstrong k
  linarith

end Endpoints

/-! ## The pointwise operator-norm endpoint over real scalars

`DavisKahan/Sources/DavisKahan1970/TanTwoThetaUnboundedResidual.lean` states the
operator-norm case of the unbounded residual `tan 2Θ` theorem over `ℂ` in a
different *shape* from the gauge endpoints above: it is a **pointwise** vector
inequality on the spectral subspace `1_{(-∞, c]}(A)`, it carries the explicit
pole-exclusion constant `κ = δ / √(δ² + 4‖B‖²)` as a second conclusion, and it
assumes **no** cutoff net and **no** hypothesis `‖sin 2Θ₀‖ < 1` — the cutoffs are
built from the spectral measure and the pole exclusion is proved, not assumed.

So the real counterpart below is *not* the `k = 1` case of
`gap_mul_kyFan_reflectionTangentCorner_le_two_mul_kyFan_ambient_real`: that
endpoint bounds the gauge of a *tangent operator* whose very existence needs
`hS1`, and its right-hand side is a Ky Fan gauge, not `‖B‖ ‖cos 2Θ₀ x‖`.  What
the two do share is the descent: the pointwise complex statement transports along
exactly the same complexification, with `TauCeti.LinearPMap.realSpecRange`
supplying the real trial subspace and
`complexifySubmodule_realSpecRange` identifying its complexification with the
complex spectral subspace the complex theorem is stated on. -/

section BlockCongr

variable {k : Type*} [RCLike k] {G : Type*} [NormedAddCommGroup G]
  [InnerProductSpace k G]

/-- **The even reflection block depends on the subspace only through its value.**
`Submodule.HasOrthogonalProjection` is a `Prop`, so once the two subspaces are
equal their instance arguments are definitionally equal too.  This is the
substitute for `rw`, whose motive is not type correct across an equality of
subspaces that occurs in an instance argument. -/
theorem diagonalPart_congr {U V : Submodule k G} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (h : U = V) (T : G →L[k] G) :
    U.diagonalPart T = V.diagonalPart T := by
  subst h
  rfl

/-- The odd reflection block depends on the subspace only through its value. -/
theorem offDiagonalPart_congr {U V : Submodule k G} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (h : U = V) (T : G →L[k] G) :
    U.offDiagonalPart T = V.offDiagonalPart T := by
  subst h
  rfl

end BlockCongr

section RealResidualOpNorm

variable {A : E →ₗ.[ℝ] E} {B Z : E →L[ℝ] E} {a b c : ℝ}

/-- **Davis--Kahan Section 7, the `tan 2Θ` theorem for an unbounded self-adjoint
operator, in residual form, at the operator norm, over real scalars.**

The real counterpart of `tanTwoTheta_unbounded_residual_opNorm_complex`, with the same
two conclusions: the tangent inequality with the sharp constant `2` against the
residual `B`, and the explicit lower bound `κ ‖x‖ ≤ ‖cos 2Θ₀ x‖` that makes it
meaningful.  As over `ℂ`, no cutoff data is assumed: the trial subspace is the
descended real spectral subspace `1_{(-∞, c]}(A)` and the cutoffs are built from
the spectral measure of the complexification.

Hypotheses, in the source's terms.  `hA` : `A` is self-adjoint.  `hB` : the
perturbation is fully off-diagonal, `H₀ = H₁ = 0`.  `hZsa`, `hZ2` : `Z` is the
self-adjoint involution `2Q - 1`.  `hZdom`, `hZcomm` : `Q` reduces `A + B`.
`hUa`, `hUb`, `hab` : the spectral separation `A ≤ a` on `𝔛₀`, `A ≥ b` on
`𝔛₁`, `a < b`. -/
theorem tanTwoTheta_unbounded_residual_opNorm_real
    (hA : _root_.IsSelfAdjoint A)
    (hB : TauCeti.IsOddFor
      (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic) B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : E), hZdom x⟩ + B (Z (x : E)) = Z (A x) + Z (B (x : E)))
    (hUa : ∀ x : A.domain,
      (x : E) ∈ TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic →
      ⟪A x, (x : E)⟫_ℝ ≤ a * ‖(x : E)‖ ^ 2)
    (hUb : ∀ x : A.domain,
      (x : E) ∈ (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic)ᗮ →
      b * ‖(x : E)‖ ^ 2 ≤ ⟪A x, (x : E)⟫_ℝ)
    (hab : a < b) {x : E}
    (hx : x ∈ TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic) :
    (b - a) *
        ‖(TauCeti.LinearPMap.realSpecRange hA (Set.Iic c)
          measurableSet_Iic).offDiagonalPart Z x‖ ≤
      2 * ‖B‖ *
        ‖(TauCeti.LinearPMap.realSpecRange hA (Set.Iic c)
          measurableSet_Iic).diagonalPart Z x‖ ∧
    TauCeti.diagonalBlockBound (b - a) ‖B‖ * ‖x‖ ≤
      ‖(TauCeti.LinearPMap.realSpecRange hA (Set.Iic c)
        measurableSet_Iic).diagonalPart Z x‖ := by
  classical
  have hAc : _root_.IsSelfAdjoint (TauCeti.LinearPMap.complexifyReal A) :=
    TauCeti.LinearPMap.isSelfAdjoint_complexifyReal hA
  have hUeq : complexifySubmodule
        (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic) =
      TauCeti.LinearPMap.specRange hAc (Set.Iic c) measurableSet_Iic :=
    complexifySubmodule_realSpecRange hA (Set.Iic c) measurableSet_Iic
  -- the transported hypotheses
  have hB' : TauCeti.IsOddFor
      (TauCeti.LinearPMap.specRange hAc (Set.Iic c) measurableSet_Iic)
      (complexify B) := hUeq ▸ isOddFor_complexifySubmodule hB
  have hZdom' := mapsDomainTo_complexifyReal hZdom
  have hZcomm' : ∀ x : (TauCeti.LinearPMap.complexifyReal A).domain,
      TauCeti.LinearPMap.complexifyReal A
          ⟨complexify Z (x : RealComplexification E), hZdom' x⟩ +
        complexify B (complexify Z (x : RealComplexification E)) =
      complexify Z (TauCeti.LinearPMap.complexifyReal A x) +
        complexify Z (complexify B (x : RealComplexification E)) := by
    intro y
    have hcoord := (TauCeti.LinearPMap.mem_complexifyReal_domain_iff A
      (y : RealComplexification E)).mp y.2
    refine RealComplexification.ext ?_ ?_
    · exact hZcomm ⟨re (y : RealComplexification E), hcoord.1⟩
    · exact hZcomm ⟨im (y : RealComplexification E), hcoord.2⟩
  have hUa' : ∀ y : (TauCeti.LinearPMap.complexifyReal A).domain,
      (y : RealComplexification E) ∈
        TauCeti.LinearPMap.specRange hAc (Set.Iic c) measurableSet_Iic →
      (⟪TauCeti.LinearPMap.complexifyReal A y,
          (y : RealComplexification E)⟫_ℂ).re ≤
        a * ‖(y : RealComplexification E)‖ ^ 2 := by
    intro y hy
    rw [← hUeq, mem_complexifySubmodule] at hy
    have hcoord := (TauCeti.LinearPMap.mem_complexifyReal_domain_iff A
      (y : RealComplexification E)).mp y.2
    have h1 := hUa ⟨re (y : RealComplexification E), hcoord.1⟩ hy.1
    have h2 := hUa ⟨im (y : RealComplexification E), hcoord.2⟩ hy.2
    have hsplit : (⟪TauCeti.LinearPMap.complexifyReal A y,
          (y : RealComplexification E)⟫_ℂ).re =
        ⟪A ⟨re (y : RealComplexification E), hcoord.1⟩,
            re (y : RealComplexification E)⟫_ℝ +
          ⟪A ⟨im (y : RealComplexification E), hcoord.2⟩,
            im (y : RealComplexification E)⟫_ℝ := rfl
    rw [hsplit, RealComplexification.norm_sq, mul_add]
    linarith
  have hUb' : ∀ y : (TauCeti.LinearPMap.complexifyReal A).domain,
      (y : RealComplexification E) ∈
        (TauCeti.LinearPMap.specRange hAc (Set.Iic c) measurableSet_Iic)ᗮ →
      b * ‖(y : RealComplexification E)‖ ^ 2 ≤
        (⟪TauCeti.LinearPMap.complexifyReal A y,
          (y : RealComplexification E)⟫_ℂ).re := by
    intro y hy
    rw [← hUeq, ← complexifySubmodule_orthogonal, mem_complexifySubmodule] at hy
    have hcoord := (TauCeti.LinearPMap.mem_complexifyReal_domain_iff A
      (y : RealComplexification E)).mp y.2
    have h1 := hUb ⟨re (y : RealComplexification E), hcoord.1⟩ hy.1
    have h2 := hUb ⟨im (y : RealComplexification E), hcoord.2⟩ hy.2
    have hsplit : (⟪TauCeti.LinearPMap.complexifyReal A y,
          (y : RealComplexification E)⟫_ℂ).re =
        ⟪A ⟨re (y : RealComplexification E), hcoord.1⟩,
            re (y : RealComplexification E)⟫_ℝ +
          ⟪A ⟨im (y : RealComplexification E), hcoord.2⟩,
            im (y : RealComplexification E)⟫_ℝ := rfl
    rw [hsplit, RealComplexification.norm_sq, mul_add]
    linarith
  have hxc : (ofReal x : RealComplexification E) ∈
      TauCeti.LinearPMap.specRange hAc (Set.Iic c) measurableSet_Iic := by
    rw [← hUeq, mem_complexifySubmodule]
    exact ⟨hx, Submodule.zero_mem _⟩
  -- the complex pointwise theorems, applied to the complexified data
  have h1 := TauCeti.gap_mul_norm_offDiagonalPart_apply_le_specRange hAc hB'
    ((complexify_isSelfAdjoint_iff Z).2 hZsa)
    (by rw [← complexify_mul, hZ2, complexify_one]) hZdom' hZcomm' hUa' hUb' hab hxc
  have h2 := TauCeti.diagonalBlockBound_mul_le_norm_diagonalPart_apply_specRange hAc hB'
    ((complexify_isSelfAdjoint_iff Z).2 hZsa)
    (by rw [← complexify_mul, hZ2, complexify_one]) hZdom' hZcomm' hUa' hUb' hab hxc
  -- and the descent
  have hoff : (TauCeti.LinearPMap.specRange hAc (Set.Iic c)
        measurableSet_Iic).offDiagonalPart (complexify Z) =
      complexify ((TauCeti.LinearPMap.realSpecRange hA (Set.Iic c)
        measurableSet_Iic).offDiagonalPart Z) := by
    rw [← offDiagonalPart_congr hUeq (complexify Z)]
    exact offDiagonalPart_complexifySubmodule _ Z
  have hdiag : (TauCeti.LinearPMap.specRange hAc (Set.Iic c)
        measurableSet_Iic).diagonalPart (complexify Z) =
      complexify ((TauCeti.LinearPMap.realSpecRange hA (Set.Iic c)
        measurableSet_Iic).diagonalPart Z) := by
    rw [← diagonalPart_congr hUeq (complexify Z)]
    exact diagonalPart_complexifySubmodule _ Z
  rw [hoff, hdiag, complexify_ofReal, complexify_ofReal, ofReal.norm_map,
    ofReal.norm_map, norm_complexify] at h1
  rw [hdiag, complexify_ofReal, ofReal.norm_map, ofReal.norm_map,
    norm_complexify] at h2
  exact ⟨h1, h2⟩

/-- The tangent form over real scalars: on the trial subspace the denominator is
nonzero, so the estimate can be divided through.
`‖sin 2Θ₀ x‖ / ‖cos 2Θ₀ x‖ ≤ 2 ‖B‖ / δ`.  The real counterpart of
`tanTwoTheta_unbounded_residual_div_complex`. -/
theorem tanTwoTheta_unbounded_residual_div_real
    (hA : _root_.IsSelfAdjoint A)
    (hB : TauCeti.IsOddFor
      (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic) B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : E), hZdom x⟩ + B (Z (x : E)) = Z (A x) + Z (B (x : E)))
    (hUa : ∀ x : A.domain,
      (x : E) ∈ TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic →
      ⟪A x, (x : E)⟫_ℝ ≤ a * ‖(x : E)‖ ^ 2)
    (hUb : ∀ x : A.domain,
      (x : E) ∈ (TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic)ᗮ →
      b * ‖(x : E)‖ ^ 2 ≤ ⟪A x, (x : E)⟫_ℝ)
    (hab : a < b) {x : E}
    (hx : x ∈ TauCeti.LinearPMap.realSpecRange hA (Set.Iic c) measurableSet_Iic)
    (hx0 : x ≠ 0) :
    ‖(TauCeti.LinearPMap.realSpecRange hA (Set.Iic c)
        measurableSet_Iic).offDiagonalPart Z x‖ /
      ‖(TauCeti.LinearPMap.realSpecRange hA (Set.Iic c)
        measurableSet_Iic).diagonalPart Z x‖ ≤ 2 * ‖B‖ / (b - a) := by
  obtain ⟨htan, hpole⟩ := tanTwoTheta_unbounded_residual_opNorm_real hA hB hZsa hZ2
    hZdom hZcomm hUa hUb hab hx
  have hδ : 0 < b - a := by linarith
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hκ : 0 < TauCeti.diagonalBlockBound (b - a) ‖B‖ := by
    rw [TauCeti.diagonalBlockBound_eq]
    have : (0 : ℝ) < √((b - a) ^ 2 + 4 * ‖B‖ ^ 2) :=
      Real.sqrt_pos.mpr (by positivity)
    positivity
  have hden : 0 < ‖(TauCeti.LinearPMap.realSpecRange hA (Set.Iic c)
      measurableSet_Iic).diagonalPart Z x‖ :=
    lt_of_lt_of_le (by positivity) hpole
  rw [div_le_div_iff₀ hden hδ]
  linarith [htan]

end RealResidualOpNorm

end

end DavisKahan1970
end TauCeti
