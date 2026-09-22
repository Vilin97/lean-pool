/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/

import LeanPool.DavisKahan.DavisKahan.TanTheta.Theorem63UnboundedInfiniteTrial
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.BoundedTruncation

/-! # Theorem63Unbounded Compression -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.Sylvester

/-!
# Theorem 6.3 with an **unbounded** Ritz compression

The Appendix to Section 6 is explicit that in the unbounded scope both `A₀ ≤ α` and
`Λ₁ ≥ α + δ` "may now be unbounded", which is why the spectral resolution of `A₀` and the
truncation `Ω(τ) A₀ Ω(τ)` appear in the printed proof at all.

`Theorem63TrialData` and `BoundedCompressionTrialBlock` permit unboundedness only in the *ambient*
operator: their `compression` is a `Z →L[𝕜] Z`, so the whole restriction of the ambient
operator to the trial space is a hypothesis-level bounded operator.  This module removes
that restriction on the tangent side.

## The data

`UnboundedCompressionTrialData Z` carries

* `compression`, a densely defined **self-adjoint closed operator on the trial space** —
  the paper's `A₀`, unbounded;
* `residual`, a **bounded** `Z →L[ℂ] H` orthogonal to the trial space — the paper's `R`.

The ambient action of a trial vector `z` in the compression domain is
`A₀ z + R z`; it is defined exactly on `A₀.domain` and is unbounded there.
`UnboundedCompressionTrialData.ofBounded` exhibits every bounded `Theorem63TrialData` as
an instance, so no hypothesis is added to anything already proved.

## The proof: truncate, then release

The two form hypotheses are the printed ones, stated on `A₀.domain`:

* `A₀ ≤ α` in form (`TauCeti.LinearPMap.SemiboundedAbove`);
* the crossed form on `Vᗮ` bounded below by `α + δ`.

For a level `τ` let `Ω(τ)` be the spectral cutoff `E_{A₀}([-τ, τ])` of the Ritz
compression and let `Z(τ) ≤ Z` be its range, viewed inside `H`.  Because `Z(τ)` is a
*spectral* subspace it **reduces** `A₀`, so on `Z(τ)`

* the compression of the ambient action is the bounded truncation `A₀ Ω(τ)`, and
* the Ritz residual of `Z(τ)` is exactly `R` restricted — the truncation contributes
  nothing to it.

So the truncated data is an ordinary bounded `Theorem63TrialData Z(τ) V`, the two form
bounds restrict to it verbatim, and the compiled Appendix chain
(`Theorem63TrialData.all_kyFan_core_of_formBounds_infinite`) applies at *arbitrary* trial
dimension with **no** finite-dimensionality hypothesis.

The fixed-cutoff conclusion contains no `τ`-dependent right-hand side — it is bounded by
`kyFanApproximationGauge k D.residual` for every `τ` — which is what makes the release
legitimate.  The cutoffs converge strongly to the identity, so the sine approximation
numbers of `Z(τ)` converge to those of `Z`
(`approximationSingularValue_comp_strongProjection_tendsto_complex`), and the levels
`τ → ∞` are unbounded, so the statement is not vacuous for a genuinely unbounded `A₀`.
-/

open scoped InnerProductSpace BigOperators Topology
open Filter

namespace TauCeti
namespace DavisKahan
namespace TanTheta

open ExactSinTheta
open TauCeti.ApproximationNumber (IsOrthogonalProjectionMap StronglyTendsto)

universe u

/-! ## The data bundle and its field-independent algebra

Everything in this section is scalar-generic: the bundle itself, the ambient action it
determines, the exhibition of every bounded bundle as an instance, and the block-algebra
passage from a chosen reducing subspace to the crossed form bound.  Only the spectral
truncation that follows is pinned to `ℂ`, and only because the projection-valued measure
it uses is. -/

section GenericScalars

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- **Trial data with an unbounded Ritz compression.**

The paper's `A₀` is a densely defined self-adjoint operator on the trial space, semibounded
above by `α` but otherwise unbounded; the paper's `R` is bounded.  Only the residual is a
bounded map here — the compression, and hence the ambient action of the trial space, is
not.

The field layout mirrors `ExactSinTheta.CommonDomainSinThetaData`, where the sine half
of the Appendix already reaches this generality. -/
structure UnboundedCompressionTrialData (Z : Submodule 𝕜 H)
    [Z.HasOrthogonalProjection] [CompleteSpace Z] where
  /-- The Ritz compression `A₀`, densely defined and self-adjoint on the trial space. -/
  compression : Z →ₗ.[𝕜] Z
  /-- `A₀` is self-adjoint. -/
  compression_isSelfAdjoint : _root_.IsSelfAdjoint compression
  /-- The bounded Ritz residual. -/
  residual : Z →L[𝕜] H
  /-- The residual is orthogonal to the trial subspace. -/
  residual_orthogonal : ∀ z z' : Z, ⟪residual z, ((z' : Z) : H)⟫_𝕜 = 0

namespace UnboundedCompressionTrialData

variable {Z : Submodule 𝕜 H} [Z.HasOrthogonalProjection] [CompleteSpace Z]

/-- The ambient action of a trial vector lying in the compression domain:
`A₀ z + R z`. -/
noncomputable def action (D : UnboundedCompressionTrialData Z)
    (z : D.compression.domain) : H :=
  ((D.compression z : Z) : H) + D.residual ((z : Z))

/-! ### The bounded data is an instance -/

/-- **Every bounded trial-block bundle is unbounded-compression data.**  No hypothesis is
added to anything already proved over `Theorem63TrialData`. -/
noncomputable def ofBounded {V : Submodule 𝕜 H} [V.HasOrthogonalProjection]
    (data : Theorem63TrialData Z V) : UnboundedCompressionTrialData Z where
  compression := (data.compression.toLinearMap.toPMap ⊤)
  compression_isSelfAdjoint :=
    TauCeti.LinearPMap.isSelfAdjoint_toPMap_top (T := _)
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr data.compression_isSymmetric)
  residual := data.residual
  residual_orthogonal := data.residual_orthogonal

omit [CompleteSpace H] in
/-- The bounded instance has the bounded bundle's residual. -/
theorem ofBounded_residual {V : Submodule 𝕜 H} [V.HasOrthogonalProjection]
    (data : Theorem63TrialData Z V) :
    (ofBounded data).residual = data.residual := rfl

omit [CompleteSpace H] in
/-- The bounded instance's compression domain is everything. -/
theorem ofBounded_compression_domain {V : Submodule 𝕜 H} [V.HasOrthogonalProjection]
    (data : Theorem63TrialData Z V) :
    (ofBounded data).compression.domain = ⊤ := rfl

omit [CompleteSpace H] in
/-- The bounded instance's ambient action is the bounded bundle's action. -/
theorem ofBounded_action {V : Submodule 𝕜 H} [V.HasOrthogonalProjection]
    (data : Theorem63TrialData Z V) (z : (ofBounded data).compression.domain) :
    (ofBounded data).action z = data.action ((z : Z)) :=
  (data.action_eq ((z : Z))).symm

omit [CompleteSpace H] [CompleteSpace Z] in
/-- The orthogonal projection onto the trial space fixes trial vectors. -/
theorem orthogonalProjectionOnto_coe (z : Z) :
    Z.orthogonalProjectionOnto ((z : Z) : H) = z :=
  Subtype.ext (Submodule.starProjection_eq_self_iff.mpr z.2)

/-! ### The printed hypotheses: a chosen reducing subspace of an ambient operator

The crossed bound the tangent chain consumes is stated at the abstraction level
`Theorem63TrialData` consumes.  The printed Theorem 6.3 states it instead as
`α + δ ≤ Λ₁ = F₁⋆ (A + H) F₁` for a *chosen* pair of complementary reducing subspaces.
The two are connected exactly as they are on the bounded side
(`TanTheta.crossed_lower_of_reducing`): by block algebra on the domain.  The link
between the data and the ambient operator is the single equation `haction` — the data's
ambient action is the ambient operator's — which encodes both `A₀ = E₀⋆ (A + H) E₀` and
`R = (A + H) E₀ - E₀ A₀`.

Nothing here touches the scalar field beyond the real part of an inner product, so it is
proved once, generically. -/

omit [CompleteSpace H] in
/-- **The crossed form bound from a chosen reducing subspace**, for unbounded-compression
trial data presented through an ambient closed operator.

`V` is a chosen subspace reducing `A` — its complementary projection preserves the domain
(`hVdom`) and commutes with the operator there (`hVcomm`) — and the quadratic form on `Vᗮ`
is bounded below by `α + δ` (`hlower`).  Nothing is assumed about `A` on `V` itself. -/
theorem crossed_lower_of_reducing
    (D : UnboundedCompressionTrialData Z)
    (V : Submodule 𝕜 H) [V.HasOrthogonalProjection]
    (A : H →ₗ.[𝕜] H)
    {α δ : ℝ}
    (hZA : ∀ z : D.compression.domain, ((z : Z) : H) ∈ A.domain)
    (haction : ∀ z : D.compression.domain,
      D.action z = A ⟨((z : Z) : H), hZA z⟩)
    (hVdom : ∀ x : A.domain, Vᗮ.starProjection ((x : H)) ∈ A.domain)
    (hVcomm : ∀ x : A.domain,
      Vᗮ.starProjection (A x) =
        A ⟨Vᗮ.starProjection ((x : H)), hVdom x⟩)
    (hlower : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (α + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_𝕜)
    (z : D.compression.domain) :
    (α + δ) * ‖Vᗮ.starProjection (((z : Z) : H))‖ ^ 2 ≤
      RCLike.re ⟪Vᗮ.starProjection (((z : Z) : H)),
        Vᗮ.starProjection (D.action z)⟫_𝕜 := by
  have hswap : ∀ a b : H, RCLike.re ⟪a, b⟫_𝕜 = RCLike.re ⟪b, a⟫_𝕜 := by
    intro a b
    conv_lhs => rw [← inner_conj_symm]
    rw [RCLike.conj_re]
  have hcomm : Vᗮ.starProjection (D.action z) =
      A ⟨Vᗮ.starProjection (((z : Z) : H)),
        hVdom ⟨((z : Z) : H), hZA z⟩⟩ := by
    rw [haction z]
    exact hVcomm ⟨((z : Z) : H), hZA z⟩
  rw [hcomm]
  exact (hlower (Vᗮ.starProjection (((z : Z) : H)))
    (Vᗮ.starProjection_apply_mem _) (hVdom ⟨((z : Z) : H), hZA z⟩)).trans_eq (hswap _ _)

end UnboundedCompressionTrialData

end GenericScalars

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

namespace UnboundedCompressionTrialData

variable {Z : Submodule ℂ H} [Z.HasOrthogonalProjection] [CompleteSpace Z]

/-! ### The spectral truncation of the Ritz compression -/

variable (D : UnboundedCompressionTrialData Z)

/-- The spectral cutoff `Ω(τ) = E_{A₀}([-τ, τ])` of the Ritz compression. -/
noncomputable def cutoff (τ : ℝ) : Z →L[ℂ] Z :=
  spectraSpectralCutoff D.compression D.compression_isSelfAdjoint τ

/-- The bounded truncation `A₀ Ω(τ)` of the Ritz compression. -/
noncomputable def trunc (τ : ℝ) : Z →L[ℂ] Z :=
  spectraBoundedTruncation D.compression D.compression_isSelfAdjoint τ

omit [CompleteSpace H] in
/-- The cutoffs are orthogonal projections. -/
theorem isOrthogonalProjectionMap_cutoff (τ : ℝ) :
    IsOrthogonalProjectionMap (D.cutoff τ) :=
  spectraSpectralCutoff_isOrthogonalProjection D.compression
    D.compression_isSelfAdjoint τ

omit [CompleteSpace H] in
/-- The cutoffs converge strongly to the identity as the level grows without bound. -/
theorem stronglyTendsto_cutoff :
    StronglyTendsto (fun τ : ℝ => D.cutoff τ) atTop
      (ContinuousLinearMap.id ℂ (Z : Type u)) := fun x =>
  spectraSpectralCutoff_tendsto_identity D.compression
    D.compression_isSelfAdjoint x

omit [CompleteSpace H] in
/-- The cutoff is idempotent. -/
theorem cutoff_cutoff (τ : ℝ) (z : Z) : D.cutoff τ (D.cutoff τ z) = D.cutoff τ z := by
  have h := (D.isOrthogonalProjectionMap_cutoff τ).1
  exact congrArg (fun L : Z →L[ℂ] Z => L z) h

omit [CompleteSpace H] in
/-- Every cutoff vector lies in the compression domain. -/
theorem cutoff_mem_domain (τ : ℝ) (z : Z) :
    D.cutoff τ z ∈ D.compression.domain :=
  spectraSpectralCutoff_range_le_domain D.compression D.compression_isSelfAdjoint τ
    ⟨z, rfl⟩

omit [CompleteSpace H] in
/-- On the cutoff range the bounded truncation is the unbounded compression. -/
theorem trunc_apply (τ : ℝ) (z : Z) :
    D.trunc τ z =
      D.compression ⟨D.cutoff τ z, D.cutoff_mem_domain τ z⟩ := by
  obtain ⟨_, hb⟩ := spectraBoundedTruncation_eq_on_cutoff D.compression
    D.compression_isSelfAdjoint τ z
  exact hb

omit [CompleteSpace H] in
/-- The truncation is symmetric. -/
theorem trunc_isSymmetric (τ : ℝ) : (D.trunc τ).IsSymmetric :=
  spectraBoundedTruncation_isSymmetric D.compression D.compression_isSelfAdjoint τ

omit [CompleteSpace H] in
/-- The cutoff absorbs the truncation on the left. -/
theorem cutoff_trunc (τ : ℝ) (z : Z) : D.cutoff τ (D.trunc τ z) = D.trunc τ z := by
  have h := (spectraBoundedTruncation_commutes_cutoff D.compression
    D.compression_isSelfAdjoint τ).2
  exact congrArg (fun L : Z →L[ℂ] Z => L z) h

omit [CompleteSpace H] in
/-- The truncation absorbs the cutoff on the right. -/
theorem trunc_cutoff (τ : ℝ) (z : Z) : D.trunc τ (D.cutoff τ z) = D.trunc τ z := by
  have h := (spectraBoundedTruncation_commutes_cutoff D.compression
    D.compression_isSelfAdjoint τ).1
  exact congrArg (fun L : Z →L[ℂ] Z => L z) h

/-! ### The truncated trial subspace -/

/-- **The truncated trial subspace**: the ambient copy of the spectral subspace `Ω(τ)Z` of
the Ritz compression. -/
noncomputable def truncSpace (τ : ℝ) : Submodule ℂ H :=
  (Z.subtypeL ∘L D.cutoff τ ∘L Z.orthogonalProjectionOnto -
    ContinuousLinearMap.id ℂ H).ker

omit [CompleteSpace H] in
/-- Membership in the truncated trial subspace is fixity under the pushed-forward
cutoff. -/
theorem mem_truncSpace_iff (τ : ℝ) (x : H) :
    x ∈ D.truncSpace τ ↔
      ((D.cutoff τ (Z.orthogonalProjectionOnto x) : Z) : H) = x := by
  change (Z.subtypeL ∘L D.cutoff τ ∘L Z.orthogonalProjectionOnto -
    ContinuousLinearMap.id ℂ H) x = 0 ↔ _
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    sub_apply, sub_eq_zero]
  rfl

/-- The truncated trial subspace is complete: it is the kernel of a bounded map. -/
instance truncSpace_completeSpace (τ : ℝ) : CompleteSpace (D.truncSpace τ) :=
  (Z.subtypeL ∘L D.cutoff τ ∘L Z.orthogonalProjectionOnto -
    ContinuousLinearMap.id ℂ H).isClosed_ker.completeSpace_coe

/-- The truncated trial subspace is orthogonally complemented. -/
noncomputable instance truncSpace_hasOrthogonalProjection (τ : ℝ) :
    (D.truncSpace τ).HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

omit [CompleteSpace H] in
/-- The truncated trial subspace sits inside the trial subspace. -/
theorem truncSpace_le (τ : ℝ) : D.truncSpace τ ≤ Z := by
  intro x hx
  rw [D.mem_truncSpace_iff τ x] at hx
  rw [← hx]
  exact (D.cutoff τ (Z.orthogonalProjectionOnto x)).2

omit [CompleteSpace H] in
/-- Every cutoff vector lies in the truncated trial subspace. -/
theorem coe_cutoff_mem_truncSpace (τ : ℝ) (z : Z) :
    ((D.cutoff τ z : Z) : H) ∈ D.truncSpace τ := by
  rw [D.mem_truncSpace_iff τ, orthogonalProjectionOnto_coe, D.cutoff_cutoff]

omit [CompleteSpace H] in
/-- The cutoff fixes every vector of the truncated trial subspace. -/
theorem cutoff_apply_of_mem_truncSpace (τ : ℝ) (f : D.truncSpace τ) :
    D.cutoff τ ⟨(f : H), D.truncSpace_le τ f.2⟩ = ⟨(f : H), D.truncSpace_le τ f.2⟩ := by
  have hx := (D.mem_truncSpace_iff τ (f : H)).mp f.2
  refine Subtype.ext ?_
  rw [show Z.orthogonalProjectionOnto ((f : H)) =
    (⟨(f : H), D.truncSpace_le τ f.2⟩ : Z) from
      Subtype.ext (Submodule.starProjection_eq_self_iff.mpr
        (D.truncSpace_le τ f.2))] at hx
  exact hx

/-- The inclusion of the truncated trial subspace into the trial subspace. -/
noncomputable def truncIncl (τ : ℝ) : D.truncSpace τ →L[ℂ] Z :=
  Theorem63TrialData.inclCLM (D.truncSpace_le τ)

omit [CompleteSpace H] in
/-- The inclusion of the truncated trial subspace does not move the ambient vector. -/
theorem truncIncl_coe (τ : ℝ) (f : D.truncSpace τ) :
    ((D.truncIncl τ f : Z) : H) = (f : H) := rfl

/-- The cutoff-corestriction of the trial subspace onto its truncation. -/
noncomputable def truncProj (τ : ℝ) : Z →L[ℂ] D.truncSpace τ :=
  (Z.subtypeL ∘L D.cutoff τ).codRestrict (D.truncSpace τ) (D.coe_cutoff_mem_truncSpace τ)

omit [CompleteSpace H] in
/-- The cutoff factors through the truncated trial subspace. -/
theorem truncIncl_truncProj (τ : ℝ) (z : Z) :
    D.truncIncl τ (D.truncProj τ z) = D.cutoff τ z := rfl

omit [CompleteSpace H] in
/-- The cutoff fixes the truncated trial subspace pointwise. -/
theorem cutoff_truncIncl (τ : ℝ) (f : D.truncSpace τ) :
    D.cutoff τ (D.truncIncl τ f) = D.truncIncl τ f :=
  D.cutoff_apply_of_mem_truncSpace τ f

omit [CompleteSpace H] in
/-- The cutoff corestriction is a contraction. -/
theorem norm_truncProj_le (τ : ℝ) : ‖D.truncProj τ‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
  rw [one_mul]
  have hcoe : ‖D.truncProj τ z‖ = ‖D.cutoff τ z‖ := rfl
  rw [hcoe]
  calc ‖D.cutoff τ z‖ ≤ ‖D.cutoff τ‖ * ‖z‖ := (D.cutoff τ).le_opNorm z
    _ ≤ 1 * ‖z‖ := by
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg z)
      exact_mod_cast (D.isOrthogonalProjectionMap_cutoff τ).norm_le_one
    _ = ‖z‖ := one_mul _

omit [CompleteSpace H] in
/-- The inclusion of the truncated trial subspace is an isometry, hence a contraction. -/
theorem norm_truncIncl_le (τ : ℝ) : ‖D.truncIncl τ‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
  rw [one_mul]
  exact le_of_eq rfl

/-! ### The bounded trial-block data on the truncated trial subspace -/

/-- The bounded action carried by the truncated trial space: `A₀ Ω(τ) + R`. -/
noncomputable def truncAction (τ : ℝ) : Z →L[ℂ] H :=
  Z.subtypeL ∘L D.trunc τ + D.residual

omit [CompleteSpace H] in
/-- The truncated action, applied. -/
theorem truncAction_apply (τ : ℝ) (z : Z) :
    D.truncAction τ z = ((D.trunc τ z : Z) : H) + D.residual z := rfl

omit [CompleteSpace H] in
/-- The truncated action is symmetric on the trial subspace: the truncation is symmetric
and the residual is orthogonal to the trial subspace. -/
theorem truncAction_symm (τ : ℝ) (z z' : Z) :
    ⟪D.truncAction τ z, ((z' : Z) : H)⟫_ℂ =
      ⟪((z : Z) : H), D.truncAction τ z'⟫_ℂ := by
  rw [truncAction_apply, truncAction_apply, inner_add_left, inner_add_right,
    D.residual_orthogonal z z',
    (by
      have h := D.residual_orthogonal z' z
      rw [← inner_conj_symm, h, map_zero] :
        ⟪((z : Z) : H), D.residual z'⟫_ℂ = 0),
    add_zero, add_zero, ← Submodule.coe_inner, ← Submodule.coe_inner]
  exact D.trunc_isSymmetric τ z z'

/-- **The bounded trial-block data on the truncated trial subspace.**  Because the
truncated subspace reduces the Ritz compression, this data's ambient action is the genuine
ambient action `A₀ z + R z` at every one of its vectors. -/
noncomputable def truncData (V : Submodule ℂ H) [V.HasOrthogonalProjection] (τ : ℝ) :
    Theorem63TrialData (D.truncSpace τ) V :=
  Theorem63TrialData.ofAction (D.truncSpace τ) V
    (D.truncAction τ ∘L D.truncIncl τ)
    (fun x y => D.truncAction_symm τ (D.truncIncl τ x) (D.truncIncl τ y))

/-- The truncated trial data acts by the truncated action. -/
theorem truncData_action (V : Submodule ℂ H) [V.HasOrthogonalProjection] (τ : ℝ)
    (f : D.truncSpace τ) :
    (D.truncData V τ).action f = D.truncAction τ (D.truncIncl τ f) := rfl

/-- **The truncated action is the true ambient action.**  On the truncated trial subspace
the bounded truncation and the unbounded compression agree, because the subspace is a
spectral subspace of the compression. -/
theorem truncData_action_eq_action (V : Submodule ℂ H) [V.HasOrthogonalProjection]
    (τ : ℝ) (f : D.truncSpace τ) :
    (D.truncData V τ).action f =
      D.action ⟨D.truncIncl τ f, D.cutoff_truncIncl τ f ▸
        D.cutoff_mem_domain τ (D.truncIncl τ f)⟩ := by
  rw [truncData_action, truncAction_apply]
  congr 1
  have h1 := D.trunc_apply τ (D.truncIncl τ f)
  have h2 : D.cutoff τ (D.truncIncl τ f) = D.truncIncl τ f := D.cutoff_truncIncl τ f
  congr 1
  rw [h1]
  congr 1
  exact Subtype.ext h2

/-- **The truncated Ritz residual is the ambient residual.**  The truncation contributes
nothing: the truncated subspace reduces the compression, so the compression's image already
lies in the subspace. -/
theorem truncData_residual (V : Submodule ℂ H) [V.HasOrthogonalProjection] (τ : ℝ) :
    (D.truncData V τ).residual = D.residual ∘L D.truncIncl τ := by
  refine ContinuousLinearMap.ext fun f => ?_
  have hres : (D.truncData V τ).residual f =
      D.truncAction τ (D.truncIncl τ f) -
        (D.truncSpace τ).starProjection (D.truncAction τ (D.truncIncl τ f)) :=
    rfl
  rw [hres, truncAction_apply]
  have hmemF : ((D.trunc τ (D.truncIncl τ f) : Z) : H) ∈ D.truncSpace τ := by
    have h := D.coe_cutoff_mem_truncSpace τ (D.trunc τ (D.truncIncl τ f))
    rwa [D.cutoff_trunc τ (D.truncIncl τ f)] at h
  have hmemperp : D.residual (D.truncIncl τ f) ∈ (D.truncSpace τ)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    have h := D.residual_orthogonal (D.truncIncl τ f) ⟨u, D.truncSpace_le τ hu⟩
    rw [← inner_conj_symm, h, map_zero]
  rw [map_add, Submodule.starProjection_eq_self_iff.mpr hmemF,
    (Submodule.starProjection_apply_eq_zero_iff (D.truncSpace τ)).mpr hmemperp]
  simp


/-! ### The two printed form bounds descend to the truncated trial subspace -/

variable (V : Submodule ℂ H) [V.HasOrthogonalProjection]

omit [CompleteSpace H] in
/-- A vector of the truncated trial subspace lies in the compression domain. -/
theorem truncIncl_mem_domain (τ : ℝ) (f : D.truncSpace τ) :
    ((D.truncIncl τ f : Z)) ∈ D.compression.domain := by
  have h := D.cutoff_mem_domain τ (D.truncIncl τ f)
  rwa [D.cutoff_truncIncl τ f] at h

omit [CompleteSpace H] in
/-- On the truncated trial subspace the bounded truncation is the unbounded
compression. -/
theorem trunc_truncIncl (τ : ℝ) (f : D.truncSpace τ) :
    D.trunc τ (D.truncIncl τ f) =
      D.compression ⟨(D.truncIncl τ f : Z), D.truncIncl_mem_domain τ f⟩ := by
  rw [D.trunc_apply τ (D.truncIncl τ f)]
  congr 1
  exact Subtype.ext (D.cutoff_truncIncl τ f)

/-- **`A₀ ≤ α` restricted.**  The printed upper form bound on the unbounded Ritz
compression descends to the bounded compression of the truncated trial data. -/
theorem truncData_compression_upper {α : ℝ}
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.compression α) (τ : ℝ) :
    ∀ f : D.truncSpace τ,
      RCLike.re ⟪(D.truncData V τ).compression f, f⟫_ℂ ≤ α * ‖f‖ ^ 2 := by
  intro f
  have hform := hupper ⟨(D.truncIncl τ f : Z), D.truncIncl_mem_domain τ f⟩
  rw [(D.truncData V τ).inner_compression_eq f, D.truncData_action V τ f,
    D.truncAction_apply τ (D.truncIncl τ f), inner_add_left]
  have hres : ⟪D.residual (D.truncIncl τ f), ((f : D.truncSpace τ) : H)⟫_ℂ = 0 :=
    D.residual_orthogonal (D.truncIncl τ f) (D.truncIncl τ f)
  rw [hres, add_zero]
  have hpair : ⟪D.trunc τ (D.truncIncl τ f), D.truncIncl τ f⟫_ℂ =
      ⟪((D.trunc τ (D.truncIncl τ f) : Z) : H),
        ((f : D.truncSpace τ) : H)⟫_ℂ := by
    rw [Submodule.coe_inner]
    rfl
  rw [← hpair, D.trunc_truncIncl τ f]
  exact hform

/-- **`α + δ ≤ Λ₁` restricted.**  The printed crossed lower form bound descends to the
truncated trial data, because the truncated action *is* the ambient action there. -/
theorem truncData_crossed_lower {α δ : ℝ}
    (hcross : ∀ z : D.compression.domain,
      (α + δ) * ‖Vᗮ.starProjection (((z : Z) : H))‖ ^ 2 ≤
        RCLike.re ⟪Vᗮ.starProjection (((z : Z) : H)),
          Vᗮ.starProjection (D.action z)⟫_ℂ) (τ : ℝ) :
    ∀ f : D.truncSpace τ,
      (α + δ) * ‖Vᗮ.starProjection (((f : D.truncSpace τ) : H))‖ ^ 2 ≤
        RCLike.re ⟪Vᗮ.starProjection (((f : D.truncSpace τ) : H)),
          Vᗮ.starProjection ((D.truncData V τ).action f)⟫_ℂ := by
  intro f
  have h := hcross ⟨(D.truncIncl τ f : Z), D.truncIncl_mem_domain τ f⟩
  have hcoe : (((⟨(D.truncIncl τ f : Z), D.truncIncl_mem_domain τ f⟩ :
      D.compression.domain) : Z) : H) = ((f : D.truncSpace τ) : H) := rfl
  rw [hcoe] at h
  have haction : (D.truncData V τ).action f =
      D.action ⟨(D.truncIncl τ f : Z), D.truncIncl_mem_domain τ f⟩ := by
    rw [D.truncData_action V τ f, D.truncAction_apply τ (D.truncIncl τ f)]
    change ((D.trunc τ (D.truncIncl τ f) : Z) : H) + _ =
      ((D.compression _ : Z) : H) + _
    rw [D.trunc_truncIncl τ f]
  rw [haction]
  exact h

/-! ### The fixed-cutoff Ky Fan estimate

The conclusion below contains **no** `τ`: the right-hand side is the Ky Fan gauge of the
ambient residual, the same for every cutoff level.  That is what makes the passage to
unbounded levels in the next section legitimate. -/

/-- **The Appendix Ky Fan estimate at a fixed cutoff level.**

The truncated trial data is bounded data, so the compiled arbitrary-trial-dimension
Appendix chain applies to it verbatim; and the truncated residual is the ambient residual,
so the bound is `τ`-free. -/
theorem all_kyFan_core_trunc {α δ : ℝ} (hδ : 0 < δ)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.compression α)
    (hcross : ∀ z : D.compression.domain,
      (α + δ) * ‖Vᗮ.starProjection (((z : Z) : H))‖ ^ 2 ≤
        RCLike.re ⟪Vᗮ.starProjection (((z : Z) : H)),
          Vᗮ.starProjection (D.action z)⟫_ℂ) (τ : ℝ) (k : ℕ) :
    δ * ∑ n ∈ Finset.range k, Real.tan (Real.arcsin
        (approximationSingularValue n
          (theorem63DirectedSineBlock (D.truncSpace τ) V))) ≤
      kyFanApproximationGauge k D.residual := by
  have hcore := (D.truncData V τ).all_kyFan_core_of_formBounds_infinite hδ
    (D.truncData_compression_upper V hupper τ) (D.truncData_crossed_lower V hcross τ) k
  refine hcore.trans ?_
  rw [D.truncData_residual V τ]
  have h := kyFanApproximationGauge_comp_le (𝕜 := ℂ) k
    (ContinuousLinearMap.id ℂ H) D.residual (D.truncIncl τ)
  rw [ContinuousLinearMap.id_comp] at h
  refine h.trans ?_
  have hnn := kyFanApproximationGauge_nonneg k D.residual
  calc
    ‖ContinuousLinearMap.id ℂ H‖ * kyFanApproximationGauge k D.residual *
        ‖D.truncIncl τ‖ ≤ 1 * kyFanApproximationGauge k D.residual * 1 := by
      refine mul_le_mul ?_ (D.norm_truncIncl_le τ) (norm_nonneg (D.truncIncl τ))
        (by positivity)
      exact mul_le_mul_of_nonneg_right ContinuousLinearMap.norm_id_le hnn
    _ = kyFanApproximationGauge k D.residual := by ring

/-! ### Releasing the cutoff -/

omit [CompleteSpace H] in
/-- The sine block of the truncated trial subspace is the ambient sine block precomposed
with the inclusion. -/
theorem truncSineBlock_eq (τ : ℝ) :
    theorem63DirectedSineBlock (D.truncSpace τ) V =
      theorem63DirectedSineBlock Z V ∘L D.truncIncl τ :=
  ContinuousLinearMap.ext fun _ => rfl

omit [CompleteSpace H] in
/-- **The truncated sine block and the cut-off ambient sine block have the same
approximation numbers.** -/
theorem approximationSingularValue_truncSineBlock (τ : ℝ) (n : ℕ) :
    approximationSingularValue n (theorem63DirectedSineBlock (D.truncSpace τ) V) =
      approximationSingularValue n
        (theorem63DirectedSineBlock Z V ∘L D.cutoff τ) := by
  set S : Z →L[ℂ] H := theorem63DirectedSineBlock Z V with hS
  have hcut : S ∘L D.cutoff τ = (S ∘L D.truncIncl τ) ∘L D.truncProj τ :=
    ContinuousLinearMap.ext fun z => by
      change S (D.cutoff τ z) = S (D.truncIncl τ (D.truncProj τ z))
      rw [D.truncIncl_truncProj τ z]
  have hincl : S ∘L D.truncIncl τ = (S ∘L D.cutoff τ) ∘L D.truncIncl τ :=
    ContinuousLinearMap.ext fun f => by
      change S (D.truncIncl τ f) = S (D.cutoff τ (D.truncIncl τ f))
      rw [D.cutoff_truncIncl τ f]
  refine le_antisymm ?_ ?_
  · rw [D.truncSineBlock_eq V τ, hincl]
    have h := approximationSingularValue_comp_le (𝕜 := ℂ) n
      (ContinuousLinearMap.id ℂ H) (S ∘L D.cutoff τ) (D.truncIncl τ)
    rw [ContinuousLinearMap.id_comp] at h
    refine h.trans ?_
    have hnn := approximationSingularValue_nonneg n (S ∘L D.cutoff τ)
    calc
      ‖ContinuousLinearMap.id ℂ H‖ * approximationSingularValue n (S ∘L D.cutoff τ) *
          ‖D.truncIncl τ‖ ≤
          1 * approximationSingularValue n (S ∘L D.cutoff τ) * 1 := by
        refine mul_le_mul ?_ (D.norm_truncIncl_le τ) (norm_nonneg (D.truncIncl τ))
          (by positivity)
        exact mul_le_mul_of_nonneg_right ContinuousLinearMap.norm_id_le hnn
      _ = approximationSingularValue n (S ∘L D.cutoff τ) := by ring
  · rw [hcut, D.truncSineBlock_eq V τ]
    have h := approximationSingularValue_comp_le (𝕜 := ℂ) n
      (ContinuousLinearMap.id ℂ H) (S ∘L D.truncIncl τ) (D.truncProj τ)
    rw [ContinuousLinearMap.id_comp] at h
    refine h.trans ?_
    have hnn := approximationSingularValue_nonneg n (S ∘L D.truncIncl τ)
    calc
      ‖ContinuousLinearMap.id ℂ H‖ * approximationSingularValue n (S ∘L D.truncIncl τ) *
          ‖D.truncProj τ‖ ≤
          1 * approximationSingularValue n (S ∘L D.truncIncl τ) * 1 := by
        refine mul_le_mul ?_ (D.norm_truncProj_le τ) (norm_nonneg (D.truncProj τ))
          (by positivity)
        exact mul_le_mul_of_nonneg_right ContinuousLinearMap.norm_id_le hnn
      _ = approximationSingularValue n (S ∘L D.truncIncl τ) := by ring

/-- **The truncated sine approximation numbers converge to the ambient ones** as the cutoff
level grows without bound. -/
theorem tendsto_approximationSingularValue_truncSineBlock (n : ℕ) :
    Filter.Tendsto (fun τ : ℝ => approximationSingularValue n
        (theorem63DirectedSineBlock (D.truncSpace τ) V)) Filter.atTop
      (nhds (approximationSingularValue n (theorem63DirectedSineBlock Z V))) := by
  have h := ApproximationNumber.approximationSingularValue_comp_strongProjection_tendsto_complex
    (P := fun τ : ℝ => D.cutoff τ) (l := Filter.atTop)
    (fun τ => D.isOrthogonalProjectionMap_cutoff τ) D.stronglyTendsto_cutoff n
    (theorem63DirectedSineBlock Z V)
  refine h.congr fun τ => ?_
  exact (D.approximationSingularValue_truncSineBlock V τ n).symm

omit [CompleteSpace H] in
/-- Every truncated sine approximation number is at most the ambient one. -/
theorem approximationSingularValue_truncSineBlock_le (τ : ℝ) (n : ℕ) :
    approximationSingularValue n (theorem63DirectedSineBlock (D.truncSpace τ) V) ≤
      approximationSingularValue n (theorem63DirectedSineBlock Z V) := by
  rw [D.approximationSingularValue_truncSineBlock V τ n]
  exact approximationSingularValue_comp_le_of_isOrthogonalProjection
    (D.isOrthogonalProjectionMap_cutoff τ) n _

/-- **No pole, with an unbounded Ritz compression.**  Every ambient directed sine
approximation number is strictly below one. -/
theorem approximationSingularValue_sineBlock_lt_one {α δ : ℝ} (hδ : 0 < δ)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.compression α)
    (hcross : ∀ z : D.compression.domain,
      (α + δ) * ‖Vᗮ.starProjection (((z : Z) : H))‖ ^ 2 ≤
        RCLike.re ⟪Vᗮ.starProjection (((z : Z) : H)),
          Vᗮ.starProjection (D.action z)⟫_ℂ) (n : ℕ) :
    approximationSingularValue n (theorem63DirectedSineBlock Z V) < 1 := by
  classical
  by_contra hcon
  have ha_le : approximationSingularValue n (theorem63DirectedSineBlock Z V) ≤ 1 := by
    refine (approximationSingularValue_le_opNorm _ _).trans ?_
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
    rw [one_mul]
    exact theorem63DirectedSineBlock_apply_norm_le Z V z
  have haeq : approximationSingularValue n (theorem63DirectedSineBlock Z V) = 1 :=
    le_antisymm ha_le (le_of_not_gt fun h => hcon h)
  set B : ℝ := kyFanApproximationGauge (n + 1) D.residual with hB_def
  have hB0 : 0 ≤ B := kyFanApproximationGauge_nonneg _ _
  set C : ℝ := B / δ + 1 with hC_def
  have hC0 : 0 ≤ C := by positivity
  set c : ℝ := Real.sin (Real.arctan C) with hc_def
  have hc0 : 0 ≤ c := Real.sin_arctan_nonneg.mpr hC0
  have hclt : c < 1 := TanArcsin.sin_arctan_lt_one C
  -- Some cutoff level already has its `n`-th sine approximation number above `c`.
  have hev := (D.tendsto_approximationSingularValue_truncSineBlock V n).eventually
    (eventually_gt_nhds (by rw [haeq]; exact hclt))
  obtain ⟨τ, hτ⟩ := hev.exists
  have hτ0 : 0 ≤ approximationSingularValue n
      (theorem63DirectedSineBlock (D.truncSpace τ) V) :=
    approximationSingularValue_nonneg _ _
  have hτ1 : approximationSingularValue n
      (theorem63DirectedSineBlock (D.truncSpace τ) V) < 1 := by
    have h := (D.truncData V τ).approximationSingularValue_sineBlock_lt_one_infiniteData
      hδ (D.truncData_compression_upper V hupper τ)
      (D.truncData_crossed_lower V hcross τ) n
    exact h
  have hmono : Real.tan (Real.arcsin c) ≤ Real.tan (Real.arcsin
      (approximationSingularValue n
        (theorem63DirectedSineBlock (D.truncSpace τ) V))) :=
    TanArcsin.tanArcsin_le_tanArcsin hc0 hτ.le hτ1
  have hsum : Real.tan (Real.arcsin
      (approximationSingularValue n
        (theorem63DirectedSineBlock (D.truncSpace τ) V))) ≤
      ∑ m ∈ Finset.range (n + 1), Real.tan (Real.arcsin
        (approximationSingularValue m
          (theorem63DirectedSineBlock (D.truncSpace τ) V))) :=
    Finset.single_le_sum
      (f := fun m => Real.tan (Real.arcsin
        (approximationSingularValue m
          (theorem63DirectedSineBlock (D.truncSpace τ) V))))
      (fun m _ => TanArcsin.tanArcsin_nonneg (approximationSingularValue_nonneg _ _))
      (Finset.self_mem_range_succ n)
  have hfinal := D.all_kyFan_core_trunc V hδ hupper hcross τ (n + 1)
  have hCval : Real.tan (Real.arcsin c) = C := TanArcsin.tanArcsin_sin_arctan C
  have hchain : δ * C ≤ B := by
    calc
      δ * C = δ * Real.tan (Real.arcsin c) := by rw [hCval]
      _ ≤ δ * ∑ m ∈ Finset.range (n + 1), Real.tan (Real.arcsin
          (approximationSingularValue m
            (theorem63DirectedSineBlock (D.truncSpace τ) V))) :=
        mul_le_mul_of_nonneg_left (hmono.trans hsum) hδ.le
      _ ≤ B := hfinal
  have hCeq : δ * C = B + δ := by
    rw [hC_def]
    field_simp
  linarith

/-- **The Appendix Ky Fan core with an unbounded Ritz compression.**

No finite-dimensionality of the trial space, and no boundedness of the Ritz compression:
only the two printed form bounds on `A₀.domain`, and a bounded residual. -/
theorem all_kyFan_core {α δ : ℝ} (hδ : 0 < δ)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.compression α)
    (hcross : ∀ z : D.compression.domain,
      (α + δ) * ‖Vᗮ.starProjection (((z : Z) : H))‖ ^ 2 ≤
        RCLike.re ⟪Vᗮ.starProjection (((z : Z) : H)),
          Vᗮ.starProjection (D.action z)⟫_ℂ) (k : ℕ) :
    δ * ∑ n ∈ Finset.range k, Real.tan (Real.arcsin
        (approximationSingularValue n (theorem63DirectedSineBlock Z V))) ≤
      kyFanApproximationGauge k D.residual := by
  classical
  have hlt := D.approximationSingularValue_sineBlock_lt_one V hδ hupper hcross
  have hsum : Filter.Tendsto
      (fun τ : ℝ => ∑ n ∈ Finset.range k, Real.tan (Real.arcsin
        (approximationSingularValue n
          (theorem63DirectedSineBlock (D.truncSpace τ) V)))) Filter.atTop
      (nhds (∑ n ∈ Finset.range k, Real.tan (Real.arcsin
        (approximationSingularValue n (theorem63DirectedSineBlock Z V))))) := by
    refine tendsto_finsetSum (Finset.range k) fun n _ => ?_
    exact (TanArcsin.continuousAt_tanArcsin
      (approximationSingularValue_nonneg n (theorem63DirectedSineBlock Z V))
      (hlt n)).tendsto.comp
      (D.tendsto_approximationSingularValue_truncSineBlock V n)
  have hmul : Filter.Tendsto
      (fun τ : ℝ => δ * ∑ n ∈ Finset.range k, Real.tan (Real.arcsin
        (approximationSingularValue n
          (theorem63DirectedSineBlock (D.truncSpace τ) V)))) Filter.atTop
      (nhds (δ * ∑ n ∈ Finset.range k, Real.tan (Real.arcsin
        (approximationSingularValue n (theorem63DirectedSineBlock Z V))))) :=
    hsum.const_mul δ
  refine le_of_tendsto hmul ?_
  filter_upwards [] with τ
  exact D.all_kyFan_core_trunc V hδ hupper hcross τ k

/-! ### The endpoint -/

/-- **Davis--Kahan Theorem 6.3 with an unbounded Ritz compression, at every Fan-dominant
unitarily invariant ideal gauge.**

This is the Appendix's stated scope for the tangent family: `A₀ ≤ α` and `Λ₁ ≥ α + δ` with
**both** allowed to be unbounded, the residual `R` bounded, and the trial space of
arbitrary dimension. -/
theorem ideal_of_formBounds
    (N : ExactSinTheta.KyFanDominantIdealFamily (𝕜 := ℂ))
    {α δ : ℝ} (hδ : 0 < δ)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.compression α)
    (hcross : ∀ z : D.compression.domain,
      (α + δ) * ‖Vᗮ.starProjection (((z : Z) : H))‖ ^ 2 ≤
        RCLike.re ⟪Vᗮ.starProjection (((z : Z) : H)),
          Vᗮ.starProjection (D.action z)⟫_ℂ)
    (tanTheta0 : Z →L[ℂ] H)
    (htan : HasTheorem63DirectedTangentApproximationNumbersInfinite Z V tanTheta0)
    (hResidual : N.Mem D.residual) :
    N.Mem tanTheta0 ∧ δ * N.gauge tanTheta0 ≤ N.gauge D.residual := by
  refine ExactSinTheta.mem_and_scaled_gauge_le_of_all_scaled_kyFan_le N.toFanDominantIdealFamily hδ
    hResidual fun k => ?_
  have hcore := D.all_kyFan_core V hδ hupper hcross k
  have hKyTan : kyFanApproximationGauge k tanTheta0 =
      ∑ n ∈ Finset.range k, Real.tan (Real.arcsin
        (approximationSingularValue n (theorem63DirectedSineBlock Z V))) := by
    unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
    refine Finset.sum_congr rfl fun n _ => ?_
    have h := htan n
    unfold approximationSingularValue at h
    exact h
  rw [hKyTan]
  exact hcore

/-- **The same endpoint with the tangent representative exhibited.**  The representative
carries exactly the paper's approximation numbers `tan θₙ`, and the `sin θₙ < 1` it needs
is derived from the two form bounds rather than assumed. -/
theorem ideal_of_formBounds_exists
    (N : ExactSinTheta.KyFanDominantIdealFamily (𝕜 := ℂ))
    {α δ : ℝ} (hδ : 0 < δ)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.compression α)
    (hcross : ∀ z : D.compression.domain,
      (α + δ) * ‖Vᗮ.starProjection (((z : Z) : H))‖ ^ 2 ≤
        RCLike.re ⟪Vᗮ.starProjection (((z : Z) : H)),
          Vᗮ.starProjection (D.action z)⟫_ℂ)
    (hResidual : N.Mem D.residual) :
    ∃ tanTheta0 : Z →L[ℂ] H,
      HasTheorem63DirectedTangentApproximationNumbersInfinite Z V tanTheta0 ∧
      N.Mem tanTheta0 ∧
      δ * N.gauge tanTheta0 ≤ N.gauge D.residual := by
  obtain ⟨tanTheta0, htan⟩ :=
    exists_hasTheorem63DirectedTangentApproximationNumbersInfinite Z V
      (D.approximationSingularValue_sineBlock_lt_one V hδ hupper hcross)
  obtain ⟨hmem, hbound⟩ := D.ideal_of_formBounds V N hδ hupper hcross tanTheta0 htan
    hResidual
  exact ⟨tanTheta0, htan, hmem, hbound⟩


/-! ### The printed hypotheses: a chosen reducing subspace of an ambient operator

The passage from the printed reducing-subspace hypotheses to the crossed form bound the
tangent chain consumes is `crossed_lower_of_reducing`, proved scalar-generically above. -/

/-- **Davis--Kahan Theorem 6.3 for an unbounded Ritz compression under the printed
reducing-subspace hypotheses, at every Fan-dominant unitarily invariant ideal gauge.**

The hypothesis list is the printed one:

* `hVdom`, `hVcomm` — the ranges of `F₀` and `F₁` are invariant subspaces of `A + H`;
* `hupper` — `A₀ ≤ α`, the upper end of the printed `β ≤ A₀ ≤ α`, with `A₀` now allowed to
  be **unbounded**;
* `hUnwanted` — `α + δ ≤ Λ₁ = F₁⋆ (A + H) F₁`, read as a form bound on `Vᗮ`;
* `hδ` — the printed `α < α + δ`.

There is no finite-dimensionality hypothesis on the trial space, no boundedness hypothesis
on the Ritz compression, and the compression of `A` to `V` itself is unconstrained. -/
theorem ideal_of_reducing_exists
    (N : ExactSinTheta.KyFanDominantIdealFamily (𝕜 := ℂ))
    (A : H →ₗ.[ℂ] H)
    {α δ : ℝ} (hδ : 0 < δ)
    (hZA : ∀ z : D.compression.domain, ((z : Z) : H) ∈ A.domain)
    (haction : ∀ z : D.compression.domain,
      D.action z = A ⟨((z : Z) : H), hZA z⟩)
    (hVdom : ∀ x : A.domain, Vᗮ.starProjection ((x : H)) ∈ A.domain)
    (hVcomm : ∀ x : A.domain,
      Vᗮ.starProjection (A x) =
        A ⟨Vᗮ.starProjection ((x : H)), hVdom x⟩)
    (hupper : TauCeti.LinearPMap.SemiboundedAbove D.compression α)
    (hUnwanted : ∀ y ∈ Vᗮ, ∀ hy : y ∈ A.domain,
      (α + δ) * ‖y‖ ^ 2 ≤ RCLike.re ⟪A ⟨y, hy⟩, y⟫_ℂ)
    (hResidual : N.Mem D.residual) :
    ∃ tanTheta0 : Z →L[ℂ] H,
      HasTheorem63DirectedTangentApproximationNumbersInfinite Z V tanTheta0 ∧
      N.Mem tanTheta0 ∧
      δ * N.gauge tanTheta0 ≤ N.gauge D.residual :=
  D.ideal_of_formBounds_exists V N hδ hupper
    (D.crossed_lower_of_reducing V A hZA haction hVdom hVcomm hUnwanted) hResidual

end UnboundedCompressionTrialData

end TanTheta
end DavisKahan
end TauCeti
