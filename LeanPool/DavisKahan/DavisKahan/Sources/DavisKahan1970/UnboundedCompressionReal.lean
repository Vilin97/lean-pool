/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.TanTheta.Theorem63UnboundedCompression
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.DirectedUnboundedReal

/-! # Unbounded Compression Real -/

@[expose] public section

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan Theorem 6.3 with an unbounded **real** Ritz compression

`DavisKahan/TanTheta/Theorem63UnboundedCompression.lean` proves the Appendix's stated scope
for the tangent family over `ℂ`: the Ritz compression `A₀` may be unbounded, the trial space
may be infinite dimensional, and only the two printed form bounds are assumed.  This module
is its real sibling.

## What has to descend, and what does not

After the generalization performed alongside this module, the data bundle
`UnboundedCompressionTrialData`, its ambient `action`, the exhibition `ofBounded` of every
bounded bundle as an instance, and the block-algebra passage `crossed_lower_of_reducing`
from the printed reducing-subspace hypotheses are all scalar-generic.  So a *real*
unbounded-compression bundle is the same structure at `𝕜 = ℝ`, not a new one.

What is not generic is the interior of the complex proof: the spectral cutoff
`Ω(τ) = E_{A₀}([-τ, τ])` of the Ritz compression, which comes from the projection-valued
measure of `ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/` and exists only over `ℂ`.

**That cutoff is not descended here, and no real spectral cutoff is needed.**  Following
`DavisKahan/Sources/DavisKahan1970/DirectedUnboundedReal.lean`, the *data* is complexified
and the numerical conclusion descended: the cutoff is then applied to the complexified
compression, entirely inside the already-compiled complex argument.  The two places where
the transport has to be exact are the Ky Fan gauge of the residual and the approximation
numbers of the directed sine block, and complexification preserves both on the nose.

## Main results

* `complexifyUnboundedCompressionTrialData`: the complexification of a real
  unbounded-compression bundle, with the compression transported by
  `PartialMapComplexification.complexify` and then read through the canonical
  subspace adapter `complexifySubmoduleEquiv`;
* `all_kyFan_core_unboundedCompression_real`: the Appendix Ky Fan passage over real data;
* `theorem6_3_unboundedCompression_ideal_exists_real` and
  `theorem6_3_unboundedCompression_ideal_of_reducing_exists_real`: Theorem 6.3 with an
  unbounded real Ritz compression, at every real Fan-dominant unitarily invariant ideal
  gauge, with the tangent representative exhibited.
-/

namespace TauCeti
namespace DavisKahan1970

open scoped InnerProductSpace BigOperators
open TauCeti.DavisKahanExt
open TauCeti.DavisKahan
open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.DavisKahan.ExactSinTheta.ComplexificationApproximation
open TauCeti.DavisKahan.TanTheta
open TauCeti.DavisKahan.TanTheta
open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation.RealComplexification
open scoped TauCeti.CompleteSubspace

noncomputable section

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-! ## An upper form bound survives unitary conjugation -/

/-- **A quadratic-form upper bound is preserved by unitary conjugation** of a self-adjoint
closed operator.  The conjugating map is an isometry, so both the form and the norm are
carried across unchanged. -/
theorem semiboundedAbove_unitaryConjugate {G K : Type v}
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] 
    (W : G ≃ₗᵢ[ℂ] K) (A : G →ₗ.[ℂ] G)
    (hA : IsSelfAdjoint A) {c : ℝ} (hc : TauCeti.LinearPMap.SemiboundedAbove A c) :
    TauCeti.LinearPMap.SemiboundedAbove (TauCeti.DavisKahan.unitaryConjugate W A hA) c := by
  intro x
  have hx : W.symm (x : K) ∈ A.domain := x.property
  have hbound := hc ⟨W.symm (x : K), hx⟩
  have hinner : ⟪(TauCeti.DavisKahan.unitaryConjugate W A hA) x, (x : K)⟫_ℂ =
      ⟪A ⟨W.symm (x : K), hx⟩, W.symm (x : K)⟫_ℂ := by
    have hxx : (x : K) = W (W.symm (x : K)) := (W.apply_symm_apply (x : K)).symm
    conv_lhs => rw [hxx]
    exact W.inner_map_map _ _
  have hnorm : ‖(x : K)‖ = ‖W.symm (x : K)‖ := (W.symm.norm_map (x : K)).symm
  rw [hinner, hnorm]
  exact hbound

/-! ## Complexifying real unbounded-compression trial data -/

variable {Z V : Submodule ℝ E} [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- **The complexification of a real unbounded-compression bundle.**

The compression is complexified coordinatewise as a closed operator and then read through
the canonical adapter `complexifySubmoduleEquiv` between `RealComplexification ↥Z` and
`↥(complexifySubmodule Z)`; the residual, being bounded, is complexified and read through
the same adapter.  No ambient operator enters. -/
def complexifyUnboundedCompressionTrialData
    (D : UnboundedCompressionTrialData Z) :
    UnboundedCompressionTrialData (complexifySubmodule Z) where
  compression :=
    TauCeti.DavisKahan.unitaryConjugate (complexifySubmoduleEquiv Z)
      (ExactSinTheta.PartialMapComplexification.complexify D.compression)
      (ExactSinTheta.PartialMapComplexification.isSelfAdjoint_complexify
        D.compression_isSelfAdjoint)
  compression_isSelfAdjoint :=
    TauCeti.DavisKahan.unitaryConjugate_isSelfAdjoint _ _ _
  residual :=
    complexify D.residual ∘L
      (complexifySubmoduleEquiv Z).symm.toContinuousLinearEquiv.toContinuousLinearMap
  residual_orthogonal := by
    intro w w'
    have hperp : ∀ z : Z, D.residual z ∈ Zᗮ := by
      intro z
      rw [Submodule.mem_orthogonal]
      intro y hy
      rw [real_inner_comm]
      exact D.residual_orthogonal z ⟨y, hy⟩
    set e := complexifySubmoduleEquiv Z with he
    set u := e.symm w with hu
    have hmem : complexify D.residual u ∈ complexifySubmodule Zᗮ := by
      rw [mem_complexifySubmodule]
      exact ⟨hperp _, hperp _⟩
    rw [complexifySubmodule_orthogonal] at hmem
    exact Submodule.inner_left_of_mem_orthogonal w'.2 hmem

/-- The complexified residual, applied: the real residual complexified and read through the
trial-subspace adapter. -/
@[simp] theorem complexifyUnboundedCompressionTrialData_residual_apply
    (D : UnboundedCompressionTrialData Z) (w : complexifySubmodule Z) :
    (complexifyUnboundedCompressionTrialData D).residual w =
      complexify D.residual ((complexifySubmoduleEquiv Z).symm w) := rfl

/-- The real coordinate of a complexified-data domain vector, as a vector of the real
compression's domain. -/
def complexifyDomainRe (D : UnboundedCompressionTrialData Z)
    (w : (complexifyUnboundedCompressionTrialData D).compression.domain) :
    D.compression.domain :=
  ⟨re ((complexifySubmoduleEquiv Z).symm (w : complexifySubmodule Z)),
    (((ExactSinTheta.PartialMapComplexification.mem_complexify_domain_iff
      D.compression _).mp w.property).1)⟩

/-- The imaginary coordinate of a complexified-data domain vector. -/
def complexifyDomainIm (D : UnboundedCompressionTrialData Z)
    (w : (complexifyUnboundedCompressionTrialData D).compression.domain) :
    D.compression.domain :=
  ⟨im ((complexifySubmoduleEquiv Z).symm (w : complexifySubmodule Z)),
    (((ExactSinTheta.PartialMapComplexification.mem_complexify_domain_iff
      D.compression _).mp w.property).2)⟩

/-- **The complexified ambient action is the real one, coordinatewise.**  Real part. -/
theorem re_action_complexifyUnboundedCompressionTrialData
    (D : UnboundedCompressionTrialData Z)
    (w : (complexifyUnboundedCompressionTrialData D).compression.domain) :
    re ((complexifyUnboundedCompressionTrialData D).action w) =
      D.action (complexifyDomainRe D w) := rfl

/-- **The complexified ambient action is the real one, coordinatewise.**  Imaginary
part. -/
theorem im_action_complexifyUnboundedCompressionTrialData
    (D : UnboundedCompressionTrialData Z)
    (w : (complexifyUnboundedCompressionTrialData D).compression.domain) :
    im ((complexifyUnboundedCompressionTrialData D).action w) =
      D.action (complexifyDomainIm D w) := rfl

/-! ## Exact transport of the finite Ky Fan data -/

/-- Approximation singular values of the residual are exactly preserved by the
complexification of unbounded-compression data. -/
theorem approximationSingularValue_complexifyUnboundedCompressionTrialData_residual
    (D : UnboundedCompressionTrialData Z) (n : ℕ) :
    approximationSingularValue n (complexifyUnboundedCompressionTrialData D).residual =
      approximationSingularValue n D.residual := by
  let U := LinearIsometryEquiv.refl ℂ (RealComplexification E)
  let W := complexifySubmoduleEquiv Z
  have hcoord :
      U.toContinuousLinearEquiv.toContinuousLinearMap ∘L
          complexify D.residual ∘L
          W.symm.toContinuousLinearEquiv.toContinuousLinearMap =
        (complexifyUnboundedCompressionTrialData D).residual := by
    apply ContinuousLinearMap.ext
    intro z
    rfl
  have hsame := SameApproximationSingularValues.of_isometricEquiv_comp U W hcoord
  exact (hsame n).symm.trans (approximationSingularValue_complexify D.residual n)

/-- The finite Ky Fan gauge of the residual is exactly preserved. -/
theorem kyFanApproximationGauge_complexifyUnboundedCompressionTrialData_residual
    (D : UnboundedCompressionTrialData Z) (k : ℕ) :
    kyFanApproximationGauge k (complexifyUnboundedCompressionTrialData D).residual =
      kyFanApproximationGauge k D.residual := by
  unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
  exact Finset.sum_congr rfl fun n _ =>
    approximationSingularValue_complexifyUnboundedCompressionTrialData_residual D n

/-! ## Transport of the two printed form bounds -/

/-- The unbounded compression's upper form bound transports to the complexified data with
the same constant. -/
theorem complexifyUnboundedCompressionTrialData_compression_upper
    (D : UnboundedCompressionTrialData Z) {alpha : ℝ}
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.compression alpha) :
    TauCeti.LinearPMap.SemiboundedAbove (complexifyUnboundedCompressionTrialData D).compression
      alpha :=
  semiboundedAbove_unitaryConjugate (complexifySubmoduleEquiv Z)
    (ExactSinTheta.PartialMapComplexification.complexify D.compression)
    (ExactSinTheta.PartialMapComplexification.isSelfAdjoint_complexify
      D.compression_isSelfAdjoint)
    (ExactSinTheta.PartialMapComplexification.semiboundedAbove_complexify hupper)

/-- The crossed form bound transports to the complexified data with the same constant. -/
theorem complexifyUnboundedCompressionTrialData_crossed_lower
    (D : UnboundedCompressionTrialData Z) {c : ℝ}
    (hcross : ∀ z : D.compression.domain,
      c * ‖Vᗮ.starProjection (((z : Z) : E))‖ ^ 2 ≤
        ⟪Vᗮ.starProjection (((z : Z) : E)), Vᗮ.starProjection (D.action z)⟫_ℝ)
    (w : (complexifyUnboundedCompressionTrialData D).compression.domain) :
    c * ‖(complexifySubmodule V)ᗮ.starProjection
        (((w : complexifySubmodule Z) : RealComplexification E))‖ ^ 2 ≤
      RCLike.re ⟪(complexifySubmodule V)ᗮ.starProjection
          (((w : complexifySubmodule Z) : RealComplexification E)),
        (complexifySubmodule V)ᗮ.starProjection
          ((complexifyUnboundedCompressionTrialData D).action w)⟫_ℂ := by
  set e := complexifySubmoduleEquiv Z with he
  set u := e.symm (w : complexifySubmodule Z) with hu
  have hcoe : ((w : complexifySubmodule Z) : RealComplexification E) =
      complexify Z.subtypeL u := by
    rw [hu, ← coe_complexifySubmoduleEquiv_eq_complexify_subtypeL Z (e.symm _),
      e.apply_symm_apply]
  rw [hcoe, starProjection_complexifySubmodule_orthogonal,
    ← ContinuousLinearMap.comp_apply, ← complexify_comp]
  have hre : RCLike.re ⟪complexify (Vᗮ.starProjection ∘L Z.subtypeL) u,
      complexify Vᗮ.starProjection
        ((complexifyUnboundedCompressionTrialData D).action w)⟫_ℂ =
      ⟪Vᗮ.starProjection (((complexifyDomainRe D w : Z) : E)),
          Vᗮ.starProjection (D.action (complexifyDomainRe D w))⟫_ℝ +
        ⟪Vᗮ.starProjection (((complexifyDomainIm D w : Z) : E)),
          Vᗮ.starProjection (D.action (complexifyDomainIm D w))⟫_ℝ := rfl
  have hnorm : ‖complexify (Vᗮ.starProjection ∘L Z.subtypeL) u‖ ^ 2 =
      ‖Vᗮ.starProjection (((complexifyDomainRe D w : Z) : E))‖ ^ 2 +
        ‖Vᗮ.starProjection (((complexifyDomainIm D w : Z) : E))‖ ^ 2 :=
    RealComplexification.norm_sq _
  rw [hre, hnorm]
  have h1 := hcross (complexifyDomainRe D w)
  have h2 := hcross (complexifyDomainIm D w)
  nlinarith [h1, h2]

/-! ## The real Ky Fan core with an unbounded real Ritz compression -/

/-- **The Appendix Ky Fan passage over real unbounded-compression data.**

No finite-dimensionality of the trial space, no boundedness of the Ritz compression, and no
real spectral cutoff: the cutoff of the printed proof is applied to the *complexified*
compression inside the compiled complex argument, and only the numerical conclusion is
descended. -/
theorem all_kyFan_core_unboundedCompression_real
    (D : UnboundedCompressionTrialData Z) (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.compression alpha)
    (hcross : ∀ z : D.compression.domain,
      (alpha + delta) * ‖Vᗮ.starProjection (((z : Z) : E))‖ ^ 2 ≤
        ⟪Vᗮ.starProjection (((z : Z) : E)), Vᗮ.starProjection (D.action z)⟫_ℝ)
    (k : ℕ) :
    delta * ∑ n ∈ Finset.range k, Real.tan (Real.arcsin
        (approximationSingularValue n (theorem63DirectedSineBlockReal Z V))) ≤
      kyFanApproximationGauge k D.residual := by
  have hcore := (complexifyUnboundedCompressionTrialData D).all_kyFan_core
    (complexifySubmodule V) hdelta
    (complexifyUnboundedCompressionTrialData_compression_upper D hupper)
    (complexifyUnboundedCompressionTrialData_crossed_lower D hcross) k
  rwa [kyFanApproximationGauge_complexifyUnboundedCompressionTrialData_residual D k,
    Finset.sum_congr rfl (fun n (_ : n ∈ Finset.range k) => by
      rw [approximationSingularValue_theorem63DirectedSineBlock_complexify Z V n])] at hcore

/-- Under the two printed form bounds every real directed sine approximation value is
strictly below one, so the real tangent sequence has no pole at any trial dimension. -/
theorem approximationSingularValue_sineBlockReal_lt_one_unboundedCompression
    (D : UnboundedCompressionTrialData Z) (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.compression alpha)
    (hcross : ∀ z : D.compression.domain,
      (alpha + delta) * ‖Vᗮ.starProjection (((z : Z) : E))‖ ^ 2 ≤
        ⟪Vᗮ.starProjection (((z : Z) : E)), Vᗮ.starProjection (D.action z)⟫_ℝ)
    (n : ℕ) :
    approximationSingularValue n (theorem63DirectedSineBlockReal Z V) < 1 := by
  have hlt := (complexifyUnboundedCompressionTrialData D)
    |>.approximationSingularValue_sineBlock_lt_one (complexifySubmodule V) hdelta
    (complexifyUnboundedCompressionTrialData_compression_upper D hupper)
    (complexifyUnboundedCompressionTrialData_crossed_lower D hcross) n
  rwa [approximationSingularValue_theorem63DirectedSineBlock_complexify Z V n] at hlt

/-! ## The endpoints -/

/-- **Davis--Kahan Theorem 6.3 with an unbounded *real* Ritz compression, at every real
Fan-dominant unitarily invariant ideal gauge**, with the tangent representative exhibited.

This is the Appendix's stated scope for the tangent family over a real Hilbert space:
`A₀ ≤ α` and `Λ₁ ≥ α + δ` with **both** allowed to be unbounded, the residual `R` bounded,
and the trial space of arbitrary dimension. -/
theorem theorem6_3_unboundedCompression_ideal_exists_real
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (D : UnboundedCompressionTrialData Z) (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.compression alpha)
    (hcross : ∀ z : D.compression.domain,
      (alpha + delta) * ‖Vᗮ.starProjection (((z : Z) : E))‖ ^ 2 ≤
        ⟪Vᗮ.starProjection (((z : Z) : E)), Vᗮ.starProjection (D.action z)⟫_ℝ)
    (hResidual : N.Mem D.residual) :
    ∃ tanTheta0 : Z →L[ℝ] E,
      HasTheorem63DirectedTangentApproximationNumbersInfiniteReal Z V tanTheta0 ∧
      N.Mem tanTheta0 ∧
      delta * N.gauge tanTheta0 ≤ N.gauge D.residual := by
  obtain ⟨tanTheta0, htan⟩ :=
    exists_hasTheorem63DirectedTangentApproximationNumbersReal Z V
      (fun n => approximationSingularValue_sineBlockReal_lt_one_unboundedCompression
        D V hdelta hupper hcross n)
  have hky : ∀ k : ℕ,
      delta * kyFanApproximationGauge k tanTheta0 ≤
        kyFanApproximationGauge k D.residual := by
    intro k
    have hcore := all_kyFan_core_unboundedCompression_real D V hdelta hupper hcross k
    have htanKy : kyFanApproximationGauge k tanTheta0 =
        ∑ n ∈ Finset.range k, Real.tan (Real.arcsin
          (approximationSingularValue n (theorem63DirectedSineBlockReal Z V))) := by
      unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
      exact Finset.sum_congr rfl fun n _ => htan n
    rw [htanKy]
    exact hcore
  obtain ⟨hmem, hbound⟩ :=
    mem_and_scaled_gauge_le_of_all_scaled_kyFan_le N.toFanDominantIdealFamily hdelta hResidual hky
  exact ⟨tanTheta0, htan, hmem, hbound⟩

/-- The same endpoint when a real tangent representative with the paper's approximation
numbers is supplied by the caller. -/
theorem theorem6_3_unboundedCompression_ideal_real
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (D : UnboundedCompressionTrialData Z) (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.compression alpha)
    (hcross : ∀ z : D.compression.domain,
      (alpha + delta) * ‖Vᗮ.starProjection (((z : Z) : E))‖ ^ 2 ≤
        ⟪Vᗮ.starProjection (((z : Z) : E)), Vᗮ.starProjection (D.action z)⟫_ℝ)
    (tanTheta0 : Z →L[ℝ] E)
    (htan : HasTheorem63DirectedTangentApproximationNumbersInfiniteReal Z V tanTheta0)
    (hResidual : N.Mem D.residual) :
    N.Mem tanTheta0 ∧ delta * N.gauge tanTheta0 ≤ N.gauge D.residual := by
  refine mem_and_scaled_gauge_le_of_all_scaled_kyFan_le N.toFanDominantIdealFamily hdelta
    hResidual fun k => ?_
  have hcore := all_kyFan_core_unboundedCompression_real D V hdelta hupper hcross k
  have htanKy : kyFanApproximationGauge k tanTheta0 =
      ∑ n ∈ Finset.range k, Real.tan (Real.arcsin
        (approximationSingularValue n (theorem63DirectedSineBlockReal Z V))) := by
    unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
    exact Finset.sum_congr rfl fun n _ => htan n
  rw [htanKy]
  exact hcore

/-- **Davis--Kahan Theorem 6.3 for an unbounded real Ritz compression under the printed
reducing-subspace hypotheses**, at every real Fan-dominant unitarily invariant ideal gauge.

The hypothesis list is the printed one:

* `hVdom`, `hVcomm` — the ranges of `F₀` and `F₁` are invariant subspaces of `A + H`;
* `hupper` — `A₀ ≤ α`, the upper end of the printed `β ≤ A₀ ≤ α`, with `A₀` now allowed to
  be **unbounded**;
* `hUnwanted` — `α + δ ≤ Λ₁ = F₁⋆ (A + H) F₁`, read as a form bound on `Vᗮ`;
* `hdelta` — the printed `α < α + δ`.

Everything is real: the ambient space, the ambient operator, the unbounded compression, the
trial and reducing subspaces, the tangent representative, and the ideal gauge. -/
theorem theorem6_3_unboundedCompression_ideal_of_reducing_exists_real
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (D : UnboundedCompressionTrialData Z) (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    (A : E →ₗ.[ℝ] E)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hZA : ∀ z : D.compression.domain, ((z : Z) : E) ∈ A.domain)
    (haction : ∀ z : D.compression.domain,
      D.action z = A ⟨((z : Z) : E), hZA z⟩)
    (hVdom : ∀ x : A.domain, Vᗮ.starProjection ((x : E)) ∈ A.domain)
    (hVcomm : ∀ x : A.domain,
      Vᗮ.starProjection (A x) =
        A ⟨Vᗮ.starProjection ((x : E)), hVdom x⟩)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.compression alpha)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ ⟪A ⟨y, hy⟩, y⟫_ℝ)
    (hResidual : N.Mem D.residual) :
    ∃ tanTheta0 : Z →L[ℝ] E,
      HasTheorem63DirectedTangentApproximationNumbersInfiniteReal Z V tanTheta0 ∧
      N.Mem tanTheta0 ∧
      delta * N.gauge tanTheta0 ≤ N.gauge D.residual :=
  theorem6_3_unboundedCompression_ideal_exists_real N D V hdelta hupper
    (fun z => by
      simpa using D.crossed_lower_of_reducing V A hZA haction hVdom hVcomm
        (fun y hy hydom => by simpa using hUnwanted y hy hydom) z)
    hResidual

end

end DavisKahan1970
end TauCeti
