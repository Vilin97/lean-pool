/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculusTransport
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.OperatorRealAlgebra
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.RealContinuousFunctionalCalculus
public import LeanPool.DavisKahan.ForTauCeti.Analysis.RCLike.ScalarTransport
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.ScalarTransport

/-!
# Real continuous functional calculus at an arbitrary `RCLike` field

```text
ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint
```

for **every** `RCLike 𝕜` and every `𝕜`-Hilbert space `E`, at unrestricted dimension.

Mathlib registers this at `𝕜 = ℂ`, through the `C⋆`-algebra structure of `E →L[ℂ] E`;
`ForTauCeti/Analysis/InnerProductSpace/RealContinuousFunctionalCalculus.lean` registers it at
`𝕜 = ℝ`, by descending the complex calculus along the complexification.  Every `RCLike` field
is isomorphic to one of those two, so the general case is a transport — of the calculus
itself, not of an existential witness.

## What this removes

Scalar-generic operator modules are stated over an arbitrary `RCLike` field but built on real
functional calculus, and historically carried

```text
[Algebra ℝ (E →L[𝕜] E)] [IsScalarTower ℝ 𝕜 (E →L[𝕜] E)]
[ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint]
```

in every signature.  None of those is a mathematical hypothesis of any theorem that carries
them: the first two are restriction of scalars (`ContinuousLinearMap.realAlgebra`), and the
third is this file.  A caller of a scalar-generic theorem should supply `[RCLike 𝕜]` and the
mathematics, and nothing else.

## The shape of the argument

`ScalarTransport e E` is `E` with the `𝕂`-structure induced through a field isomorphism
`e : RCLikeIso 𝕜 𝕂`, and `ScalarTransport.clm` carries operators across.  It is a bijection
that preserves composition, the adjoint and the norm, so it is an isometric `ℝ`-`⋆`-algebra
isomorphism `(E →L[𝕜] E) ≃⋆ₐ[ℝ] (ScalarTransport e E →L[𝕂] ScalarTransport e E)`, and
`ContinuousFunctionalCalculus.of_starAlgEquiv` moves the calculus back along it.

`RCLike.I_eq_zero_or_im_I_eq_one` supplies the isomorphism, to `ℝ` or to `ℂ`.  This is the
same two-case dispatch that `ContinuousLinearMap.hasMinMaxLowerBoundEverywhere` and
`TauCeti.DavisKahan.Sylvester.hasUnboundedSylvesterKyFan` already use, and it lands in the same
place: an instance, discharged once, invisible to every caller.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: none.  Written directly here, 2026-09-03.
* Extraction class: **new**.  It depends on `RCLike/ScalarTransport.lean`,
  `InnerProductSpace/RealContinuousFunctionalCalculus.lean` and
  `CStarAlgebra/ContinuousFunctionalCalculusTransport.lean`, all of which are in `ForTauCeti`.
* Namespace: `TauCeti.ScalarTransport` for the isomorphism, `ContinuousLinearMap` for the
  instance, matching the objects they are about.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none**.
-/

public section

open scoped InnerProductSpace

attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower

universe u w v

namespace TauCeti
namespace ScalarTransport

variable {𝕜 : Type u} {𝕂 : Type w} [RCLike 𝕜] [RCLike 𝕂] {e : RCLikeIso 𝕜 𝕂}
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The transport preserves composition: it does not move the underlying functions. -/
@[simp] theorem clm_mul (S T : E →L[𝕜] E) :
    clm (e := e) (S * T) = clm (e := e) S * clm (e := e) T := rfl

omit [CompleteSpace E] in
/-- The transport preserves the identity operator. -/
@[simp] theorem clm_one : clm (e := e) (1 : E →L[𝕜] E) = 1 := rfl

omit [CompleteSpace E] in
/-- The transport is additive. -/
@[simp] theorem clm_add (S T : E →L[𝕜] E) :
    clm (e := e) (S + T) = clm (e := e) S + clm (e := e) T := rfl

omit [CompleteSpace E] in
/-- The transport is semilinear along `e`: a `𝕜`-scalar becomes its image. -/
@[simp] theorem clm_smul (c : 𝕜) (T : E →L[𝕜] E) :
    clm (e := e) (c • T) = e c • clm (e := e) T := by
  refine ContinuousLinearMap.ext fun x => ?_
  change of (e := e) (c • T (out x)) = e c • of (e := e) (T (out x))
  rw [smul_def, e.toRingEquiv.symm_apply_apply]
  rfl

omit [CompleteSpace E] in
/-- The transport is `ℝ`-homogeneous.  Both sides act by restriction of scalars along their
own `algebraMap` from `ℝ`, and `e` fixes the reals. -/
@[simp] theorem clm_real_smul (r : ℝ) (T : E →L[𝕜] E) :
    clm (e := e) (r • T) = r • clm (e := e) T := by
  have h1 : (r • T : E →L[𝕜] E) = (algebraMap ℝ 𝕜 r) • T := (algebraMap_smul 𝕜 r T).symm
  have h2 : (r • clm (e := e) T) = (algebraMap ℝ 𝕂 r) • clm (e := e) T :=
    (algebraMap_smul 𝕂 r (clm (e := e) T)).symm
  rw [h1, h2, clm_smul]
  congr 1
  rw [RCLike.algebraMap_eq_ofReal, RCLike.algebraMap_eq_ofReal]
  exact e.map_ofReal r

/-- The transport is a `⋆`-map: `star` on a Hilbert-space operator algebra is the adjoint,
and `adjoint_clm` is exactly that statement. -/
@[simp] theorem clm_star (T : E →L[𝕜] E) :
    clm (e := e) (star T) = star (clm (e := e) T) := by
  change clm (e := e) (ContinuousLinearMap.adjoint T)
      = ContinuousLinearMap.adjoint (clm (e := e) T)
  exact (adjoint_clm (e := e) T).symm

/-- **The scalar transport of operators is an `ℝ`-`⋆`-algebra isomorphism.**

Composition, the adjoint and the norm are all preserved because the transport changes no
function and no metric; only the field the scalars are named in moves. -/
@[expose]
noncomputable def clmStarAlgEquiv (e : RCLikeIso 𝕜 𝕂) (E : Type v) [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] :
    (E →L[𝕜] E) ≃⋆ₐ[ℝ] (ScalarTransport e E →L[𝕂] ScalarTransport e E) where
  toFun := clm
  invFun := (clmEquiv (e := e) (E := E) (F := E)).symm
  left_inv := (clmEquiv (e := e) (E := E) (F := E)).left_inv
  right_inv := (clmEquiv (e := e) (E := E) (F := E)).right_inv
  map_mul' := clm_mul
  map_add' := clm_add
  map_star' := clm_star
  map_smul' := clm_real_smul

/-- The star-algebra equivalence acts by the operator transport `clm`. -/
@[simp] theorem clmStarAlgEquiv_apply (T : E →L[𝕜] E) :
    clmStarAlgEquiv e E T = clm (e := e) T := rfl

/-- The transport preserves the operator norm, so it is continuous. -/
theorem continuous_clmStarAlgEquiv :
    Continuous (clmStarAlgEquiv e E) :=
  AddMonoidHomClass.continuous_of_bound (clmStarAlgEquiv e E) 1 fun T => by
    rw [one_mul]
    exact le_of_eq (clm_norm (e := e) T)

/-- The transport preserves the operator norm, so its inverse is continuous.  This is the one
analytic input `ContinuousFunctionalCalculus.of_starAlgEquiv` asks for. -/
theorem continuous_clmStarAlgEquiv_symm :
    Continuous (clmStarAlgEquiv e E).symm :=
  AddMonoidHomClass.continuous_of_bound (clmStarAlgEquiv e E).symm 1 fun T => by
    have h : clm (e := e) ((clmStarAlgEquiv e E).symm T) = T :=
      (clmStarAlgEquiv e E).apply_symm_apply T
    rw [one_mul, ← clm_norm (e := e) ((clmStarAlgEquiv e E).symm T), h]

end ScalarTransport
end TauCeti

namespace ContinuousLinearMap

open TauCeti TauCeti.ScalarTransport

/-- **The continuous functional calculus over `ℝ` for self-adjoint bounded operators on a
Hilbert space over an arbitrary `RCLike` field, in unrestricted dimension.**

Proved by transport: the field is isomorphic to `ℝ` or to `ℂ`, and the calculus is already
registered at both.

Not an instance, for the reason `ContinuousLinearMap.realAlgebra` is not: its statement mentions
that real algebra structure, so it can only be activated together with it.  A consumer writes

```lean
attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal
```

and a definition elaborated under those carries them in its body. -/
theorem continuousFunctionalCalculusReal
    {𝕜 : Type u} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] :
    ContinuousFunctionalCalculus ℝ (E →L[𝕜] E) IsSelfAdjoint := by
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with h | h
  · exact ContinuousFunctionalCalculus.of_starAlgEquiv
      (clmStarAlgEquiv (RCLikeIso.real h) E) continuous_clmStarAlgEquiv_symm
      fun _ => isSelfAdjoint_clm_iff.symm
  · exact ContinuousFunctionalCalculus.of_starAlgEquiv
      (clmStarAlgEquiv (RCLikeIso.complex h) E) continuous_clmStarAlgEquiv_symm
      fun _ => isSelfAdjoint_clm_iff.symm

end ContinuousLinearMap

attribute [local instance 100] ContinuousLinearMap.continuousFunctionalCalculusReal

namespace TauCeti
namespace ScalarTransport

/-! ## What the transport does to the calculus

With the instance in place on both sides, `clm` commutes with the functional calculus.
Modulus naturality is downstream in `ForTauCeti.Analysis.InnerProductSpace.ModulusTransport`,
which keeps this file usable by the modulus definition without an import cycle. -/

variable {𝕜 : Type u} {𝕂 : Type w} [RCLike 𝕜] [RCLike 𝕂] {e : RCLikeIso 𝕜 𝕂}
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

attribute [local instance] ContinuousLinearMap.instStarOrderedRingRCLike

/-- The transport preserves the real spectrum: it is an `ℝ`-algebra isomorphism. -/
@[simp] theorem spectrum_clm (T : E →L[𝕜] E) :
    spectrum ℝ (clm (e := e) T) = spectrum ℝ T :=
  AlgEquiv.spectrum_eq (clmStarAlgEquiv e E) T

/-- The transport preserves and reflects nonnegativity. -/
@[simp] theorem nonneg_clm_iff {T : E →L[𝕜] E} : 0 ≤ clm (e := e) T ↔ 0 ≤ T := by
  constructor
  · intro h
    have hsa : IsSelfAdjoint T := isSelfAdjoint_clm_iff.1 (.of_nonneg h)
    rw [StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ hsa]
    rw [StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ (.of_nonneg h), spectrum_clm] at h
    exact h
  · intro h
    have hsa : IsSelfAdjoint (clm (e := e) T) := isSelfAdjoint_clm_iff.2 (.of_nonneg h)
    rw [StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ hsa, spectrum_clm]
    rw [StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) _ (.of_nonneg h)] at h
    exact h

/-- **The transport commutes with the continuous functional calculus.** -/
theorem clm_cfc (f : ℝ → ℝ) {T : E →L[𝕜] E} (hT : IsSelfAdjoint T)
    (hf : ContinuousOn f (spectrum ℝ T)) :
    clm (e := e) (cfc f T) = cfc f (clm (e := e) T) :=
  ContinuousFunctionalCalculus.map_cfc (clmStarAlgEquiv e E)
    continuous_clmStarAlgEquiv (fun _ => isSelfAdjoint_clm_iff.symm) f hT hf


/-! ## Reflections and reflected subspaces

The reflection in a subspace is `2 P - 1`, so the transport carries it, and hence carries the
image of one subspace under the reflection in another.  That image is the object the
Davis--Kahan double-angle statements are about. -/

omit [CompleteSpace E] in
/-- The transport carries the reflection operator of a subspace. -/
@[simp] theorem reflectionOperator_clm (S : Submodule 𝕜 E) [S.HasOrthogonalProjection] :
    (submodule (e := e) S).reflectionOperator = clm (e := e) S.reflectionOperator := by
  rw [Submodule.reflectionOperator_eq_two_smul_sub_id,
    Submodule.reflectionOperator_eq_two_smul_sub_id, two_smul, two_smul, starProjection_clm,
    clm_sub, clm_add]
  rfl

end ScalarTransport
end TauCeti
