/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.DirectedReal
public import LeanPool.DavisKahan.DavisKahan.TanTheta.Theorem63UnboundedInfiniteTrial
public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.Real.SpectralRestriction

/-! # Directed Unbounded Real -/

@[expose] public section

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan Theorem 6.3 for an unbounded real self-adjoint operator

`DavisKahan/Sources/DavisKahan1970/DirectedReal.lean` transports the *bounded* directed
tangent theorem to a real Hilbert space.  This module does the same for the **unbounded**
scope claim of Section 2, at arbitrary trial dimension and at every real Fan-dominant
unitarily invariant ideal gauge.

## What actually has to descend

The unbounded tangent chain consumes its ambient operator only through
`Theorem63TrialData` -- the bounded triple (action, compression, Ritz residual) tied by the
block identity -- together with the two printed form bounds.  That bundle, the closed
operator carrying it (`BoundedCompressionTrialBlock`), the reassembly
`Theorem63TrialData.ofUnbounded`, and the decoupling `crossed_lower_of_reducing` are all
scalar-generic, and are stated over `RCLike` in their own modules.

Exactly one link is not: `Theorem63TrialData.all_kyFan_core_of_formBounds_infinite`, the
Appendix Ky Fan passage, whose finite-projector selection step rests on the bounded
projection-valued measure of `ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/`, which
exists only over `ℂ` in the pinned dependencies.  That single link is what this module
transports, exactly as `DirectedReal.lean` transports its bounded counterpart: at the
finite Ky Fan level, where approximation numbers are preserved on the nose by
complexification, so no scalar-fixed ideal family is ever compared across fields.

The tangent representative is then built over the *real* trial space by
`exists_hasTheorem63DirectedTangentApproximationNumbersReal`, and the real ideal gauge is
recovered by real Fan dominance.

## Main results

* `complexifyTrialData`: the complexification of real trial-block data;
* `theorem6_3_all_kyFan_core_infiniteData_real`: the Ky Fan tangent inequalities over real
  trial-block data at arbitrary trial dimension;
* `theorem6_3_unbounded_infiniteTrial_ideal_exists_of_reducing_real`: the printed
  Theorem 6.3 for a closed unbounded real self-adjoint operator, an arbitrary complete real
  trial subspace, and an arbitrary chosen reducing subspace, with the tangent
  representative exhibited.
-/

namespace TauCeti
namespace DavisKahan1970

open scoped InnerProductSpace BigOperators
open TauCeti.DavisKahanExt
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

/-! ## Complexifying real trial-block data -/

variable {Z V : Submodule ℝ E} [Z.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- **The complexification of real Theorem 6.3 trial-block data.**

Every field is bounded, so each is complexified coordinatewise and then read through the
canonical adapter `complexifySubmoduleEquiv` between `RealComplexification ↥Z` and
`↥(complexifySubmodule Z)`.  No ambient operator, bounded or unbounded, enters. -/
def complexifyTrialData (data : Theorem63TrialData Z V) :
    Theorem63TrialData (complexifySubmodule Z) (complexifySubmodule V) where
  action := complexify data.action ∘L
    (complexifySubmoduleEquiv Z).symm.toContinuousLinearEquiv.toContinuousLinearMap
  compression :=
    (complexifySubmoduleEquiv Z).toContinuousLinearEquiv.toContinuousLinearMap ∘L
      complexify data.compression ∘L
      (complexifySubmoduleEquiv Z).symm.toContinuousLinearEquiv.toContinuousLinearMap
  residual := complexify data.residual ∘L
    (complexifySubmoduleEquiv Z).symm.toContinuousLinearEquiv.toContinuousLinearMap
  compression_isSymmetric := by
    intro x y
    have hsym : (complexify data.compression).IsSymmetric :=
      (complexify_isSymmetric_iff data.compression).2 data.compression_isSymmetric
    set e := complexifySubmoduleEquiv Z with he
    change ⟪e (complexify data.compression (e.symm x)), y⟫_ℂ =
      ⟪x, e (complexify data.compression (e.symm y))⟫_ℂ
    calc ⟪e (complexify data.compression (e.symm x)), y⟫_ℂ
        = ⟪e (complexify data.compression (e.symm x)), e (e.symm y)⟫_ℂ := by
          rw [e.apply_symm_apply]
      _ = ⟪complexify data.compression (e.symm x), e.symm y⟫_ℂ := e.inner_map_map _ _
      _ = ⟪e.symm x, complexify data.compression (e.symm y)⟫_ℂ := hsym _ _
      _ = ⟪e (e.symm x), e (complexify data.compression (e.symm y))⟫_ℂ :=
          (e.inner_map_map _ _).symm
      _ = ⟪x, e (complexify data.compression (e.symm y))⟫_ℂ := by rw [e.apply_symm_apply]
  action_eq := by
    have hreal : data.action = Z.subtypeL ∘L data.compression + data.residual := by
      apply ContinuousLinearMap.ext
      intro w
      exact data.action_eq w
    intro z
    set e := complexifySubmoduleEquiv Z with he
    set u := e.symm z with hu
    change complexify data.action u =
      ((e (complexify data.compression u) : complexifySubmodule Z) :
        RealComplexification E) + complexify data.residual u
    rw [coe_complexifySubmoduleEquiv_eq_complexify_subtypeL Z
      (complexify data.compression u), ← ContinuousLinearMap.comp_apply,
      ← complexify_comp, hreal, complexify_add]
    rfl
  residual_orthogonal := by
    intro z z'
    set e := complexifySubmoduleEquiv Z with he
    set u := e.symm z with hu
    have hmem : complexify data.residual u ∈ complexifySubmodule Zᗮ := by
      rw [mem_complexifySubmodule]
      exact ⟨data.residual_mem_orthogonal _, data.residual_mem_orthogonal _⟩
    rw [complexifySubmodule_orthogonal] at hmem
    exact Submodule.inner_left_of_mem_orthogonal z'.2 hmem

omit [CompleteSpace E] in
/-- The complexified residual, applied: the real residual complexified and read through the
trial-subspace adapter. -/
@[simp] theorem complexifyTrialData_residual_apply (data : Theorem63TrialData Z V)
    (z : complexifySubmodule Z) :
    (complexifyTrialData data).residual z =
      complexify data.residual ((complexifySubmoduleEquiv Z).symm z) := rfl

omit [CompleteSpace E] in
/-- The complexified action, applied: the real action complexified and read through the
trial-subspace adapter. -/
@[simp] theorem complexifyTrialData_action_apply (data : Theorem63TrialData Z V)
    (z : complexifySubmodule Z) :
    (complexifyTrialData data).action z =
      complexify data.action ((complexifySubmoduleEquiv Z).symm z) := rfl

/-! ## Exact transport of the finite Ky Fan data -/

/-- Approximation singular values of the residual are exactly preserved by the
complexification of trial-block data. -/
theorem approximationSingularValue_complexifyTrialData_residual
    (data : Theorem63TrialData Z V) (n : ℕ) :
    approximationSingularValue n (complexifyTrialData data).residual =
      approximationSingularValue n data.residual := by
  let U := LinearIsometryEquiv.refl ℂ (RealComplexification E)
  let W := complexifySubmoduleEquiv Z
  have hcoord :
      U.toContinuousLinearEquiv.toContinuousLinearMap ∘L
          complexify data.residual ∘L
          W.symm.toContinuousLinearEquiv.toContinuousLinearMap =
        (complexifyTrialData data).residual := by
    apply ContinuousLinearMap.ext
    intro z
    rfl
  have hsame := SameApproximationSingularValues.of_isometricEquiv_comp U W hcoord
  exact (hsame n).symm.trans (approximationSingularValue_complexify data.residual n)

/-- The finite Ky Fan gauge of the residual is exactly preserved by the complexification of
trial-block data. -/
theorem kyFanApproximationGauge_complexifyTrialData_residual
    (data : Theorem63TrialData Z V) (k : ℕ) :
    kyFanApproximationGauge k (complexifyTrialData data).residual =
      kyFanApproximationGauge k data.residual := by
  unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
  exact Finset.sum_congr rfl fun n _ =>
    approximationSingularValue_complexifyTrialData_residual data n

/-! ## Transport of the two printed form bounds -/

omit [CompleteSpace E] in
/-- The compression form bound transports to the complexified data with the same
constant. -/
theorem complexifyTrialData_compression_upper (data : Theorem63TrialData Z V)
    {alpha : ℝ} (hMupper : ∀ z : Z, ⟪data.compression z, z⟫_ℝ ≤ alpha * ‖z‖ ^ 2)
    (w : complexifySubmodule Z) :
    RCLike.re ⟪(complexifyTrialData data).compression w, w⟫_ℂ ≤ alpha * ‖w‖ ^ 2 := by
  set e := complexifySubmoduleEquiv Z with he
  set u := e.symm w with hu
  have hw : e u = w := e.apply_symm_apply w
  have hnorm : ‖w‖ = ‖u‖ := by rw [← hw]; exact e.norm_map u
  have hinner : ⟪(complexifyTrialData data).compression w, w⟫_ℂ =
      ⟪complexify data.compression u, u⟫_ℂ := by
    change ⟪e (complexify data.compression u), w⟫_ℂ = _
    rw [← hw]
    exact e.inner_map_map _ _
  rw [hinner, hnorm, re_inner_complexify, norm_sq]
  have h1 := hMupper (re u)
  have h2 := hMupper (im u)
  nlinarith [h1, h2]

omit [CompleteSpace E] in
/-- The crossed form bound transports to the complexified data with the same constant. -/
theorem complexifyTrialData_crossed_lower (data : Theorem63TrialData Z V)
    {c : ℝ}
    (hcross : ∀ z : Z, c * ‖Vᗮ.starProjection ((z : Z) : E)‖ ^ 2 ≤
      ⟪Vᗮ.starProjection ((z : Z) : E), Vᗮ.starProjection (data.action z)⟫_ℝ)
    (w : complexifySubmodule Z) :
    c * ‖(complexifySubmodule V)ᗮ.starProjection ((w : complexifySubmodule Z) :
        RealComplexification E)‖ ^ 2 ≤
      RCLike.re ⟪(complexifySubmodule V)ᗮ.starProjection
          ((w : complexifySubmodule Z) : RealComplexification E),
        (complexifySubmodule V)ᗮ.starProjection
          ((complexifyTrialData data).action w)⟫_ℂ := by
  set e := complexifySubmoduleEquiv Z with he
  set u := e.symm w with hu
  have hw : e u = w := e.apply_symm_apply w
  have hcoe : ((w : complexifySubmodule Z) : RealComplexification E) =
      complexify Z.subtypeL u := by
    rw [← hw]
    exact coe_complexifySubmoduleEquiv_eq_complexify_subtypeL Z u
  have hact : (complexifyTrialData data).action w = complexify data.action u := rfl
  rw [hcoe, hact, starProjection_complexifySubmodule_orthogonal,
    ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply,
    ← complexify_comp, ← complexify_comp]
  have hre : RCLike.re ⟪complexify (Vᗮ.starProjection ∘L Z.subtypeL) u,
      complexify (Vᗮ.starProjection ∘L data.action) u⟫_ℂ =
      ⟪Vᗮ.starProjection ((re u : Z) : E),
          Vᗮ.starProjection (data.action (re u))⟫_ℝ +
        ⟪Vᗮ.starProjection ((im u : Z) : E),
          Vᗮ.starProjection (data.action (im u))⟫_ℝ := rfl
  have hnorm : ‖complexify (Vᗮ.starProjection ∘L Z.subtypeL) u‖ ^ 2 =
      ‖Vᗮ.starProjection ((re u : Z) : E)‖ ^ 2 +
        ‖Vᗮ.starProjection ((im u : Z) : E)‖ ^ 2 := by
    exact norm_sq _
  rw [hre, hnorm]
  have h1 := hcross (re u)
  have h2 := hcross (im u)
  nlinarith [h1, h2]

/-! ## The real Ky Fan core over real trial-block data -/

/-- **The Appendix Ky Fan passage over real trial-block data.**

This is the one link of the unbounded tangent chain that is not scalar-generic; it is
transported here at the finite Ky Fan level, where complexification preserves approximation
numbers exactly.  There is no dimension hypothesis on the trial space. -/
theorem theorem6_3_all_kyFan_core_infiniteData_real (data : Theorem63TrialData Z V)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hMupper : ∀ z : Z, ⟪data.compression z, z⟫_ℝ ≤ alpha * ‖z‖ ^ 2)
    (hcross : ∀ z : Z, (alpha + delta) * ‖Vᗮ.starProjection ((z : Z) : E)‖ ^ 2 ≤
      ⟪Vᗮ.starProjection ((z : Z) : E), Vᗮ.starProjection (data.action z)⟫_ℝ)
    (k : ℕ) :
    delta * ∑ n ∈ Finset.range k, Real.tan (Real.arcsin
        (approximationSingularValue n (theorem63DirectedSineBlockReal Z V))) ≤
      kyFanApproximationGauge k data.residual := by
  have hcore := (complexifyTrialData data).all_kyFan_core_of_formBounds_infinite
    hdelta (complexifyTrialData_compression_upper data hMupper)
    (complexifyTrialData_crossed_lower data hcross) k
  rwa [kyFanApproximationGauge_complexifyTrialData_residual data k,
    Finset.sum_congr rfl (fun n (_ : n ∈ Finset.range k) => by
      rw [approximationSingularValue_theorem63DirectedSineBlock_complexify Z V n])] at hcore

/-- Under the two printed form bounds every real directed sine approximation value is
strictly below one, so the real tangent sequence has no pole at any trial dimension. -/
theorem approximationSingularValue_sineBlockReal_lt_one_infiniteData
    (data : Theorem63TrialData Z V)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hMupper : ∀ z : Z, ⟪data.compression z, z⟫_ℝ ≤ alpha * ‖z‖ ^ 2)
    (hcross : ∀ z : Z, (alpha + delta) * ‖Vᗮ.starProjection ((z : Z) : E)‖ ^ 2 ≤
      ⟪Vᗮ.starProjection ((z : Z) : E), Vᗮ.starProjection (data.action z)⟫_ℝ)
    (n : ℕ) :
    approximationSingularValue n (theorem63DirectedSineBlockReal Z V) < 1 := by
  have hlt := (complexifyTrialData data).approximationSingularValue_sineBlock_lt_one_infiniteData
    hdelta (complexifyTrialData_compression_upper data hMupper)
    (complexifyTrialData_crossed_lower data hcross) n
  rwa [approximationSingularValue_theorem63DirectedSineBlock_complexify Z V n] at hlt

/-- **Theorem 6.3 at every real Fan-dominant ideal gauge, over real trial-block data**, with
the tangent representative exhibited and its membership concluded. -/
theorem theorem6_3_ideal_infiniteData_exists_real
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (data : Theorem63TrialData Z V)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hMupper : ∀ z : Z, ⟪data.compression z, z⟫_ℝ ≤ alpha * ‖z‖ ^ 2)
    (hcross : ∀ z : Z, (alpha + delta) * ‖Vᗮ.starProjection ((z : Z) : E)‖ ^ 2 ≤
      ⟪Vᗮ.starProjection ((z : Z) : E), Vᗮ.starProjection (data.action z)⟫_ℝ)
    (hResidual : N.Mem data.residual) :
    ∃ tanTheta0 : Z →L[ℝ] E,
      HasTheorem63DirectedTangentApproximationNumbersInfiniteReal Z V tanTheta0 ∧
      N.Mem tanTheta0 ∧
      delta * N.gauge tanTheta0 ≤ N.gauge data.residual := by
  obtain ⟨tanTheta0, htan⟩ :=
    exists_hasTheorem63DirectedTangentApproximationNumbersReal Z V
      (fun n => approximationSingularValue_sineBlockReal_lt_one_infiniteData
        data hdelta hMupper hcross n)
  have hky : ∀ k : ℕ,
      delta * kyFanApproximationGauge k tanTheta0 ≤
        kyFanApproximationGauge k data.residual := by
    intro k
    have hcore := theorem6_3_all_kyFan_core_infiniteData_real data hdelta hMupper hcross k
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
theorem theorem6_3_ideal_infiniteData_real
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (data : Theorem63TrialData Z V)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hMupper : ∀ z : Z, ⟪data.compression z, z⟫_ℝ ≤ alpha * ‖z‖ ^ 2)
    (hcross : ∀ z : Z, (alpha + delta) * ‖Vᗮ.starProjection ((z : Z) : E)‖ ^ 2 ≤
      ⟪Vᗮ.starProjection ((z : Z) : E), Vᗮ.starProjection (data.action z)⟫_ℝ)
    (tanTheta0 : Z →L[ℝ] E)
    (htan : HasTheorem63DirectedTangentApproximationNumbersInfiniteReal Z V tanTheta0)
    (hResidual : N.Mem data.residual) :
    N.Mem tanTheta0 ∧ delta * N.gauge tanTheta0 ≤ N.gauge data.residual := by
  refine mem_and_scaled_gauge_le_of_all_scaled_kyFan_le N.toFanDominantIdealFamily hdelta
    hResidual fun k => ?_
  have hcore := theorem6_3_all_kyFan_core_infiniteData_real data hdelta hMupper hcross k
  have htanKy : kyFanApproximationGauge k tanTheta0 =
      ∑ n ∈ Finset.range k, Real.tan (Real.arcsin
        (approximationSingularValue n (theorem63DirectedSineBlockReal Z V))) := by
    unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
    exact Finset.sum_congr rfl fun n _ => htan n
  rw [htanKy]
  exact hcore

/-! ## Davis--Kahan Theorem 6.3 for an unbounded real self-adjoint operator

The hypothesis list below is the printed one (transcription, Theorem 6.3; Section 2
`tan Θ` hypotheses):

* `hVdom`, `hVcomm` — the chosen `V = Range F₀` and its complement `Vᗮ = Range F₁` reduce
  the ambient operator: the projection onto `Vᗮ` preserves the domain and commutes with
  the operator there;
* `hCompression` — `A₀ = E₀* (A + H) E₀ ≤ α`, the upper end of the printed `β ≤ A₀ ≤ α`;
* `hUnwanted` — `α + δ ≤ Λ₁ = F₁* (A + H) F₁`, read as a form bound on `Vᗮ`;
* `hδ` — the printed `α < α + δ`.

The compression of the operator to `V` itself is unconstrained, exactly as in the source,
and no interval of the ambient spectrum is required to be empty. -/

variable [CompleteSpace Z]

/-- **Davis--Kahan Theorem 6.3 over a real Hilbert space, for a closed unbounded real
self-adjoint operator, an arbitrary complete real trial subspace, and a chosen reducing
subspace, at every real Fan-dominant unitarily invariant ideal gauge.**

The tangent representative is exhibited with the paper's complete singular-value sequence,
its membership in the chosen ideal is concluded rather than assumed, and the conclusion is
the printed `δ N(tan Θ₀) ≤ N(R)`.

Nothing here is a complex theorem with real hypotheses: the ambient space, the operator,
the trial and reducing subspaces, the tangent representative and the ideal gauge are all
real.  Only the Appendix Ky Fan passage is proved by complexification, at the finite Ky Fan
level where approximation numbers are preserved exactly. -/
theorem theorem6_3_unbounded_infiniteTrial_ideal_exists_of_reducing_real
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (A : E →ₗ.[ℝ] E)
    (D : BoundedCompressionTrialBlock A Z)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hVdom : ∀ x : A.domain, Vᗮ.starProjection ((x : E)) ∈ A.domain)
    (hVcomm : ∀ x : A.domain,
      Vᗮ.starProjection (A x) =
        A ⟨Vᗮ.starProjection ((x : E)), hVdom x⟩)
    (hCompression : ∀ z : Z, ⟪D.operator z, z⟫_ℝ ≤ alpha * ‖z‖ ^ 2)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ ⟪A ⟨y, hy⟩, y⟫_ℝ)
    (hResidual : N.Mem D.residual) :
    ∃ tanTheta0 : Z →L[ℝ] E,
      HasTheorem63DirectedTangentApproximationNumbersInfiniteReal Z V tanTheta0 ∧
      N.Mem tanTheta0 ∧
      delta * N.gauge tanTheta0 ≤ N.gauge D.residual :=
  theorem6_3_ideal_infiniteData_exists_real N (Theorem63TrialData.ofUnbounded D V) hdelta
    hCompression
    (fun z => by
      simpa using crossed_lower_of_reducing (𝕜 := ℝ) A D V hVdom hVcomm
        (fun y hy hydom => by simpa using hUnwanted y hy hydom) z)
    hResidual

/-- The same unbounded real theorem when a real tangent representative with the paper's
approximation numbers is supplied by the caller. -/
theorem theorem6_3_unbounded_infiniteTrial_ideal_of_reducing_real
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (A : E →ₗ.[ℝ] E)
    (D : BoundedCompressionTrialBlock A Z)
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hVdom : ∀ x : A.domain, Vᗮ.starProjection ((x : E)) ∈ A.domain)
    (hVcomm : ∀ x : A.domain,
      Vᗮ.starProjection (A x) =
        A ⟨Vᗮ.starProjection ((x : E)), hVdom x⟩)
    (hCompression : ∀ z : Z, ⟪D.operator z, z⟫_ℝ ≤ alpha * ‖z‖ ^ 2)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (alpha + delta) * ‖y‖ ^ 2 ≤ ⟪A ⟨y, hy⟩, y⟫_ℝ)
    (tanTheta0 : Z →L[ℝ] E)
    (htan : HasTheorem63DirectedTangentApproximationNumbersInfiniteReal Z V tanTheta0)
    (hResidual : N.Mem D.residual) :
    N.Mem tanTheta0 ∧ delta * N.gauge tanTheta0 ≤ N.gauge D.residual :=
  theorem6_3_ideal_infiniteData_real N (Theorem63TrialData.ofUnbounded D V) hdelta
    hCompression
    (fun z => by
      simpa using crossed_lower_of_reducing (𝕜 := ℝ) A D V hVdom hVcomm
        (fun y hy hydom => by simpa using hUnwanted y hy hydom) z)
    tanTheta0 htan hResidual

/-! ## The spectral-gap specialization over a real Hilbert space

At `V = ` the real spectral range of `Set.Iic α`, the printed reducing hypotheses are
supplied by the real spectral layer of
`DavisKahan/SpectralTheory/Real/SpectralRestriction.lean`, and the printed form bound
`α + δ ≤ Λ₁` is supplied by a real spectral gap. -/

section SpectralGap

open TauCeti.DavisKahan.RealSpectralRestriction

variable (A : E →ₗ.[ℝ] E) (hA : IsSelfAdjoint A)

omit [CompleteSpace E] [CompleteSpace Z] in
private theorem starProjection_congr_real {U W : Submodule ℝ E}
    [U.HasOrthogonalProjection] [W.HasOrthogonalProjection] (h : U = W) (y : E) :
    U.starProjection y = W.starProjection y := by
  subst h
  rfl

/-- The orthogonal complement of a real spectral range projects with the real spectral
projection of the complementary set. -/
theorem starProjection_orthogonal_realSelfAdjointSpectralSubspace
    (S : Set ℝ) (hS : MeasurableSet S) :
    (realSelfAdjointSpectralSubspace A hA S hS)ᗮ.starProjection =
      realSelfAdjointSpectralProjection A hA Sᶜ hS.compl := by
  apply ContinuousLinearMap.ext
  intro y
  rw [realSelfAdjointSpectralProjection_eq_starProjection A hA Sᶜ hS.compl]
  exact (starProjection_congr_real
    (realSelfAdjointSpectralSubspace_compl A hA S hS) y).symm

/-- **A real spectral range reduces its operator, domain half.** -/
theorem orthogonal_realSelfAdjointSpectralSubspace_starProjection_mem_domain
    (S : Set ℝ) (hS : MeasurableSet S) (x : A.domain) :
    (realSelfAdjointSpectralSubspace A hA S hS)ᗮ.starProjection ((x : E)) ∈ A.domain := by
  rw [starProjection_orthogonal_realSelfAdjointSpectralSubspace A hA S hS]
  exact realSelfAdjointSpectralProjection_mem_domain A hA hS.compl x

/-- **A real spectral range reduces its operator, commutation half.** -/
theorem realSelfAdjoint_apply_orthogonal_realSelfAdjointSpectralSubspace_starProjection
    (S : Set ℝ) (hS : MeasurableSet S) (x : A.domain) :
    (realSelfAdjointSpectralSubspace A hA S hS)ᗮ.starProjection (A x) =
      A
        ⟨(realSelfAdjointSpectralSubspace A hA S hS)ᗮ.starProjection ((x : E)),
          orthogonal_realSelfAdjointSpectralSubspace_starProjection_mem_domain
            A hA S hS x⟩ := by
  have hproj := starProjection_orthogonal_realSelfAdjointSpectralSubspace A hA S hS
  have hcoe :
      (⟨(realSelfAdjointSpectralSubspace A hA S hS)ᗮ.starProjection ((x : E)),
        orthogonal_realSelfAdjointSpectralSubspace_starProjection_mem_domain
          A hA S hS x⟩ : A.domain) =
      ⟨realSelfAdjointSpectralProjection A hA Sᶜ hS.compl ((x : E)),
        realSelfAdjointSpectralProjection_mem_domain A hA hS.compl x⟩ :=
    Subtype.ext (congrArg (fun L : E →L[ℝ] E => L ((x : E))) hproj)
  rw [hcoe, realSelfAdjoint_apply_spectralProjection A hA hS.compl x, hproj]

/-- **The real spectral gap supplies the printed form lower bound on the unwanted
subspace.**

The complex counterpart is proved by a threshold argument through the open gap; here it is
transported to the real operator along the canonical real copy `ofReal`, on which the
complexified closed operator acts by the original real operator and the complexified
spectral projection acts by the descended real one. -/
theorem le_re_inner_of_mem_orthogonal_realSelfAdjointSpectralSubspace_of_gap
    {alpha delta : ℝ}
    (hgap : realSelfAdjointSpectralProjection A hA (Set.Ioo alpha (alpha + delta))
      measurableSet_Ioo = 0)
    (y : E)
    (hyV : y ∈ (realSelfAdjointSpectralSubspace A hA (Set.Iic alpha)
      measurableSet_Iic)ᗮ)
    (hy : y ∈ A.domain) :
    (alpha + delta) * ‖y‖ ^ 2 ≤ ⟪A ⟨y, hy⟩, y⟫_ℝ := by
  classical
  set Ac := PartialMapComplexification.complexify A with hAc_def
  have hAc : _root_.IsSelfAdjoint Ac :=
    PartialMapComplexification.isSelfAdjoint_complexify hA
  -- The complex gap hypothesis, obtained by complexifying the real one.
  have hgapC : TauCeti.LinearPMap.specProjection hAc
      (Set.Ioo alpha (alpha + delta)) measurableSet_Ioo = 0 := by
    have h := complexify_realSelfAdjointSpectralProjection A hA
      (Set.Ioo alpha (alpha + delta)) measurableSet_Ioo
    rw [hgap] at h
    exact h.symm.trans RealComplexification.complexify_zero
  -- The real copy of `y` lies in the complexified domain.
  have hydC : ofReal y ∈ Ac.domain :=
    (PartialMapComplexification.ofRealDomain A ⟨y, hy⟩).2
  -- The real copy of `y` is orthogonal to the complex spectral subspace of `Iic α`.
  have hyVC : ofReal y ∈
      (_root_.TauCeti.DavisKahan.selfAdjointSpectralSubspace Ac hAc
        (Set.Iic alpha) measurableSet_Iic)ᗮ := by
    rw [← complexifySubmodule_realSelfAdjointSpectralSubspace A hA (Set.Iic alpha)
      measurableSet_Iic, ← complexifySubmodule_orthogonal,
      ofReal_mem_complexifySubmodule_iff]
    exact hyV
  have hC :=
    _root_.TauCeti.DavisKahan.TanTheta.le_re_inner_of_mem_orthogonal_selfAdjointSpectralSubspace_of_gap
      Ac hAc hgapC (ofReal y) hyVC hydC
  -- Read the complex bound back on the real copy.
  have hact : Ac ⟨ofReal y, hydC⟩ = ofReal (A ⟨y, hy⟩) :=
    PartialMapComplexification.complexify_apply_ofReal A ⟨y, hy⟩
  have hnorm : ‖ofReal (E := E) y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [RealComplexification.norm_sq]
    simp
  rw [hact, hnorm, RealComplexification.inner_ofReal] at hC
  simpa using hC

/-! ### The unbounded real endpoints under a spectral gap -/

variable {alpha delta : ℝ}

/-- **Davis--Kahan Theorem 6.3 over a real Hilbert space at the canonical spectral cut.**

`V` is the real spectral range of `Set.Iic α`, and the printed `α + δ ≤ Λ₁` is replaced by
the real spectral gap: the operator has no spectrum in `Set.Ioo α (α + δ)`.  The trial
space is an arbitrary complete real subspace of the operator domain and the gauge is any
real Fan-dominant unitarily invariant ideal gauge. -/
theorem theorem6_3_unbounded_infiniteTrial_ideal_exists_real
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (D : BoundedCompressionTrialBlock A Z)
    (hdelta : 0 < delta)
    (hgap : realSelfAdjointSpectralProjection A hA (Set.Ioo alpha (alpha + delta))
      measurableSet_Ioo = 0)
    (hCompression : ∀ z : Z, ⟪D.operator z, z⟫_ℝ ≤ alpha * ‖z‖ ^ 2)
    (hResidual : N.Mem D.residual) :
    ∃ tanTheta0 : Z →L[ℝ] E,
      HasTheorem63DirectedTangentApproximationNumbersInfiniteReal Z
          (realSelfAdjointSpectralSubspace A hA (Set.Iic alpha) measurableSet_Iic)
          tanTheta0 ∧
        N.Mem tanTheta0 ∧
        delta * N.gauge tanTheta0 ≤ N.gauge D.residual :=
  theorem6_3_unbounded_infiniteTrial_ideal_exists_of_reducing_real N A D hdelta
    (orthogonal_realSelfAdjointSpectralSubspace_starProjection_mem_domain A hA
      (Set.Iic alpha) measurableSet_Iic)
    (realSelfAdjoint_apply_orthogonal_realSelfAdjointSpectralSubspace_starProjection A hA
      (Set.Iic alpha) measurableSet_Iic)
    hCompression
    (le_re_inner_of_mem_orthogonal_realSelfAdjointSpectralSubspace_of_gap A hA hgap)
    hResidual

/-- The same real spectral-gap theorem when a real tangent representative with the paper's
approximation numbers is supplied by the caller. -/
theorem theorem6_3_unbounded_infiniteTrial_ideal_real
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    (D : BoundedCompressionTrialBlock A Z)
    (hdelta : 0 < delta)
    (hgap : realSelfAdjointSpectralProjection A hA (Set.Ioo alpha (alpha + delta))
      measurableSet_Ioo = 0)
    (hCompression : ∀ z : Z, ⟪D.operator z, z⟫_ℝ ≤ alpha * ‖z‖ ^ 2)
    (tanTheta0 : Z →L[ℝ] E)
    (htan : HasTheorem63DirectedTangentApproximationNumbersInfiniteReal Z
      (realSelfAdjointSpectralSubspace A hA (Set.Iic alpha) measurableSet_Iic) tanTheta0)
    (hResidual : N.Mem D.residual) :
    N.Mem tanTheta0 ∧ delta * N.gauge tanTheta0 ≤ N.gauge D.residual :=
  theorem6_3_unbounded_infiniteTrial_ideal_of_reducing_real N A D hdelta
    (orthogonal_realSelfAdjointSpectralSubspace_starProjection_mem_domain A hA
      (Set.Iic alpha) measurableSet_Iic)
    (realSelfAdjoint_apply_orthogonal_realSelfAdjointSpectralSubspace_starProjection A hA
      (Set.Iic alpha) measurableSet_Iic)
    hCompression
    (le_re_inner_of_mem_orthogonal_realSelfAdjointSpectralSubspace_of_gap A hA hgap)
    tanTheta0 htan hResidual

end SpectralGap

end

end DavisKahan1970
end TauCeti
