/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.AngleFunctionalCalculusReal
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.ReflectionRestriction
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.SameSequence
import LeanPool.DavisKahan.ForTauCeti.Analysis.RCLike.ScalarTransportFunctionalCalculus

/-!
# The operator angle at an arbitrary `RCLike` field

`sinAngleOperator`, `angleOperator` and `sinTwoAngleOperator` are the paper's `sin Θ`, `Θ` and
`sin 2Θ` between two closed subspaces of a Hilbert space over an arbitrary `RCLike` field:

```text
sin Θ  = |P_U - P_V|            Θ = arcsin (sin Θ)          sin 2Θ = sin (2 Θ)
```

Nothing in those formulas is field-specific.  They were nevertheless written twice — over `ℂ`
by the functional calculus and over `ℝ` by descent from the complexification — because the real
continuous functional calculus was not available at an abstract field.
`ForTauCeti/Analysis/RCLike/ScalarTransportFunctionalCalculus.lean` registers it, so the
definitions below are the direct ones and carry no hypothesis beyond `[RCLike 𝕜]`.

## The two identifications

* over `ℂ` the generic definitions **are** `sinAngleOperatorC`, `angleOperatorC` and
  `sinTwoAngleOperatorC`, definitionally;
* over `ℝ` they agree with `sinAngleOperatorR`, `angleOperatorR` and `sinTwoAngleOperatorR`,
  which are defined by descent.  That is a theorem, and its content is the naturality of the
  calculus along the complexification (`TauCeti.RealComplexification.complexify_cfc` and
  `complexify_modulus`).

Those two identifications are what lets a scalar-generic theorem be proved by dispatching an
arbitrary `RCLike` field to its real-like or complex-like case and reusing the fixed-field
analytic proofs.  `clm_sinTwoAngleOperator` and its siblings carry the objects across the
scalar transport that makes the dispatch possible.
-/

namespace TauCeti
namespace DavisKahan.Angle

open DavisKahan
open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation.RealComplexification

open scoped InnerProductSpace

attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal
attribute [local instance] ContinuousLinearMap.instStarOrderedRingRCLike

noncomputable section

universe u w v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-! ## The definitions -/

/-- **The paper's `sin Θ` between two closed subspaces**, at an arbitrary `RCLike` field: the
modulus of the projector difference. -/
def sinAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E :=
  ContinuousLinearMap.modulus (U.starProjection - V.starProjection)

/-- **The paper's Hermitian operator angle `Θ = arcsin |P_U - P_V|`**, at an arbitrary `RCLike`
field. -/
def angleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E :=
  cfc Real.arcsin (sinAngleOperator U V)

/-- **The paper's ambient `sin 2Θ`**, at an arbitrary `RCLike` field. -/
def sinTwoAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E :=
  cfc (fun t : ℝ => Real.sin (2 * t)) (angleOperator U V)

variable (U V : Submodule 𝕜 E) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- **`sin Θ` is symmetric in the two subspaces.**  `|P_U - P_V| = |P_V - P_U|`,
because the modulus does not see a sign.

This is the ambient (`ContinuousLinearMap`) companion of
`TauCeti.DavisKahan.sinAngleOperator_comm`, which says the same for the
`LinearMap` spelling.  It is what makes the *ambient* estimates indifferent to
which of the two subspaces is named first -- unlike the directed quantities,
which are genuinely asymmetric. -/
theorem sinAngleOperator_comm : sinAngleOperator V U = sinAngleOperator U V := by
  have hneg : (V.starProjection - U.starProjection : E →L[𝕜] E)
      = -(U.starProjection - V.starProjection) := by abel
  rw [sinAngleOperator, sinAngleOperator, hneg, ContinuousLinearMap.modulus_neg]

/-- `Θ` is symmetric in the two subspaces. -/
theorem angleOperator_comm : angleOperator V U = angleOperator U V := by
  rw [angleOperator, angleOperator, sinAngleOperator_comm]

/-- **The ambient `sin 2Θ` is symmetric in the two subspaces.**

The source's ambient estimates are therefore indifferent to the order of the
pair, which is what lets a theorem proved with the gap on one member's blocks be
read with the roles exchanged. -/
theorem sinTwoAngleOperator_comm :
    sinTwoAngleOperator V U = sinTwoAngleOperator U V := by
  rw [sinTwoAngleOperator, sinTwoAngleOperator, angleOperator_comm]

/-- `sin Θ` is nonnegative, being a modulus. -/
theorem sinAngleOperator_nonneg : 0 ≤ sinAngleOperator U V :=
  ContinuousLinearMap.modulus_nonneg _

/-- The operator norm of the generic ambient sine is exactly the projection gap. -/
theorem norm_sinAngleOperator : ‖sinAngleOperator U V‖ = U.projectionGap V := by
  unfold sinAngleOperator Submodule.projectionGap
  exact ContinuousLinearMap.norm_modulus _

/-- `sin Θ` is self-adjoint. -/
theorem isSelfAdjoint_sinAngleOperator : IsSelfAdjoint (sinAngleOperator U V) :=
  ContinuousLinearMap.modulus_isSelfAdjoint _

/-- The operator angle is self-adjoint. -/
theorem isSelfAdjoint_angleOperator : IsSelfAdjoint (angleOperator U V) :=
  cfc_predicate Real.arcsin (sinAngleOperator U V)

/-- `sin 2Θ` is self-adjoint. -/
theorem isSelfAdjoint_sinTwoAngleOperator : IsSelfAdjoint (sinTwoAngleOperator U V) :=
  cfc_predicate _ (angleOperator U V)

/-! ## Over `ℂ`: the generic objects are the complex ones

Definitionally so: `ContinuousFunctionalCalculus` is a `Prop`, and the real algebra structure
the generic definition resolves is the restriction of scalars that `E →L[ℂ] E` already
carries. -/

section Complex

variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable (U V : Submodule ℂ F) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- Over `ℂ` the generic ambient sine *is* `sinAngleOperatorC`. -/
@[simp] theorem sinAngleOperator_complex : sinAngleOperator U V = sinAngleOperatorC U V := rfl

@[simp] theorem angleOperator_complex : angleOperator U V = angleOperatorC U V := rfl

/-- Over `ℂ` the generic ambient `sin 2Θ` *is* `sinTwoAngleOperatorC`. -/
@[simp] theorem sinTwoAngleOperator_complex :
    sinTwoAngleOperator U V = sinTwoAngleOperatorC U V := rfl

end Complex

/-! ## Over `ℝ`: the generic objects are the descended ones

Here there is something to prove.  `sinAngleOperatorR` and its siblings are *defined* as the
real parts of the complex angle operators of the complexified pair, so the identification is
the naturality of the modulus and of the calculus along `complexify`, plus injectivity of
`complexify`. -/

section Real

variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable (U V : Submodule ℝ F) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- Over `ℝ` the generic ambient sine *is* `sinAngleOperatorR`. -/
@[simp] theorem sinAngleOperator_real : sinAngleOperator U V = sinAngleOperatorR U V := by
  refine complexify_injective ?_
  rw [complexify_sinAngleOperatorR]
  change complexify (ContinuousLinearMap.modulus (U.starProjection - V.starProjection)) =
    ContinuousLinearMap.modulus
      ((complexifySubmodule U).starProjection - (complexifySubmodule V).starProjection)
  rw [complexify_modulus, starProjection_complexifySubmodule, starProjection_complexifySubmodule,
    complexify_sub]

/-- Over `ℝ` the generic ambient angle *is* `angleOperatorR`. -/
@[simp] theorem angleOperator_real : angleOperator U V = angleOperatorR U V := by
  refine complexify_injective ?_
  rw [complexify_angleOperatorR]
  change complexify (cfc Real.arcsin (sinAngleOperator U V)) = _
  rw [complexify_cfc Real.arcsin (isSelfAdjoint_sinAngleOperator U V)
      Real.continuous_arcsin.continuousOn,
    sinAngleOperator_real, complexify_sinAngleOperatorR]
  rfl

/-- Over `ℝ` the generic ambient `sin 2Θ` *is* `sinTwoAngleOperatorR`. -/
@[simp] theorem sinTwoAngleOperator_real :
    sinTwoAngleOperator U V = sinTwoAngleOperatorR U V := by
  refine complexify_injective ?_
  rw [complexify_sinTwoAngleOperatorR]
  change complexify (cfc (fun t : ℝ => Real.sin (2 * t)) (angleOperator U V)) = _
  rw [complexify_cfc _ (isSelfAdjoint_angleOperator U V)
      (by fun_prop : ContinuousOn (fun t : ℝ => Real.sin (2 * t)) _),
    angleOperator_real, complexify_angleOperatorR]
  rfl

end Real

/-! ## Across the scalar transport

`ScalarTransport e E` is `E` with the `𝕂`-structure induced by a field isomorphism
`e : RCLikeIso 𝕜 𝕂`, and `ScalarTransport.clm` carries operators across it.  These three
lemmas say the angle operators go across too, which is what turns a fixed-field theorem into a
theorem at an arbitrary `RCLike` field. -/

section Transport

variable {𝕂 : Type w} [RCLike 𝕂] {e : RCLikeIso 𝕜 𝕂}

open TauCeti.ScalarTransport

/-- The scalar transport carries the ambient sine. -/
@[simp] theorem clm_sinAngleOperator :
    clm (e := e) (sinAngleOperator U V) =
      sinAngleOperator (ScalarTransport.submodule (e := e) U)
        (ScalarTransport.submodule (e := e) V) := by
  change clm (e := e) (ContinuousLinearMap.modulus (U.starProjection - V.starProjection)) =
    ContinuousLinearMap.modulus
      ((ScalarTransport.submodule (e := e) U).starProjection -
        (ScalarTransport.submodule (e := e) V).starProjection)
  rw [clm_modulus, starProjection_clm, starProjection_clm, clm_sub]

/-- The scalar transport carries the ambient angle. -/
@[simp] theorem clm_angleOperator :
    clm (e := e) (angleOperator U V) =
      angleOperator (ScalarTransport.submodule (e := e) U)
        (ScalarTransport.submodule (e := e) V) := by
  change clm (e := e) (cfc Real.arcsin (sinAngleOperator U V)) = _
  rw [clm_cfc Real.arcsin (isSelfAdjoint_sinAngleOperator U V)
      Real.continuous_arcsin.continuousOn, clm_sinAngleOperator]
  rfl

/-- The scalar transport carries the ambient `sin 2Θ`. -/
@[simp] theorem clm_sinTwoAngleOperator :
    clm (e := e) (sinTwoAngleOperator U V) =
      sinTwoAngleOperator (ScalarTransport.submodule (e := e) U)
        (ScalarTransport.submodule (e := e) V) := by
  change clm (e := e) (cfc (fun t : ℝ => Real.sin (2 * t)) (angleOperator U V)) = _
  rw [clm_cfc _ (isSelfAdjoint_angleOperator U V)
      (by fun_prop : ContinuousOn (fun t : ℝ => Real.sin (2 * t)) _), clm_angleOperator]
  rfl

end Transport

/-! ## The directed angle

The paper's *directed* angle between an ordered pair of subspaces, as opposed to the ambient
angle above.  `sin Θ₀` and `cos Θ₀` are the moduli of the two cross-projections `Uᗮ ← U` and
`V ← U`, they commute, and `sin 2Θ₀` is `2 sin Θ₀ cos Θ₀` -- the ordinary double-angle formula,
usable because the two factors commute.

Nothing here is field-specific either, and the three definitions are the direct ones.  Over `ℂ`
they *are* `directedSinAngleOperatorC`, `directedCosAngleOperatorC` and
`directedSinTwoAngleOperatorC`; over `ℝ` the development keeps the directed operators in the
canonical complexification (`Real.directedSinTwoAngleOperatorRC` and its siblings are
*defined* as the complex ones of the complexified pair), so the identification there is stated
through `complexify`. -/

section Directed

/-- **The paper's directed `sin Θ₀`** between an ordered pair of closed subspaces, at an
arbitrary `RCLike` field: the modulus of the cross-projection `U → Uᗮ` through `V`. -/
def directedSinAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E :=
  ContinuousLinearMap.modulus (Vᗮ.starProjection ∘L U.starProjection)

/-- **The paper's directed `cos Θ₀`**, at an arbitrary `RCLike` field. -/
def directedCosAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E :=
  ContinuousLinearMap.modulus (V.starProjection ∘L U.starProjection)

/-- **The paper's directed `sin 2Θ₀`**, at an arbitrary `RCLike` field: `2 sin Θ₀ cos Θ₀`
through the commuting directed sine and cosine. -/
def directedSinTwoAngleOperator (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : E →L[𝕜] E :=
  (2 : ℝ) • (directedSinAngleOperator U V * directedCosAngleOperator U V)

/-! ### Structure of the directed angle

The three facts the definition of `sin 2Θ₀` as `2 sin Θ₀ cos Θ₀` presupposes: the two factors
are nonnegative, they commute, and therefore their product is nonnegative and self-adjoint.
Nonnegativity is immediate -- both are moduli.  Commutation is the one that has content, and it
is obtained by dispatch: it is a fact about the two cross-projections, proved over `ℂ` in
`OperatorAngleComplex.lean`, and carried to `ℝ` by `complexify` and to an arbitrary field by the
scalar transport. -/

/-- The directed sine is nonnegative: it is a modulus. -/
theorem directedSinAngleOperator_nonneg : 0 ≤ directedSinAngleOperator U V :=
  ContinuousLinearMap.modulus_nonneg _

/-- The directed cosine is nonnegative: it is a modulus. -/
theorem directedCosAngleOperator_nonneg : 0 ≤ directedCosAngleOperator U V :=
  ContinuousLinearMap.modulus_nonneg _

/-- The directed sine is self-adjoint: it is a modulus. -/
theorem isSelfAdjoint_directedSinAngleOperator :
    IsSelfAdjoint (directedSinAngleOperator U V) :=
  ContinuousLinearMap.modulus_isSelfAdjoint _

/-- The directed cosine is self-adjoint: it is a modulus. -/
theorem isSelfAdjoint_directedCosAngleOperator :
    IsSelfAdjoint (directedCosAngleOperator U V) :=
  ContinuousLinearMap.modulus_isSelfAdjoint _

section DirectedComplex

variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable (U V : Submodule ℂ F) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- Over `ℂ` the generic directed sine *is* `directedSinAngleOperatorC`. -/
@[simp] theorem directedSinAngleOperator_complex :
    directedSinAngleOperator U V = directedSinAngleOperatorC U V := rfl

/-- Over `ℂ` the generic directed cosine *is* `directedCosAngleOperatorC`. -/
@[simp] theorem directedCosAngleOperator_complex :
    directedCosAngleOperator U V = directedCosAngleOperatorC U V := rfl

/-- Over `ℂ` the generic directed `sin 2Θ₀` *is* `directedSinTwoAngleOperatorC`. -/
@[simp] theorem directedSinTwoAngleOperator_complex :
    directedSinTwoAngleOperator U V = directedSinTwoAngleOperatorC U V := rfl

end DirectedComplex

section DirectedReal

variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable (U V : Submodule ℝ F) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]

/-- Over `ℝ` the directed sine complexifies to the complex directed sine of the complexified
pair, which is where this development keeps the real directed angle. -/
@[simp] theorem complexify_directedSinAngleOperator :
    complexify (directedSinAngleOperator U V) = Real.directedSinAngleOperatorRC U V := by
  change complexify (ContinuousLinearMap.modulus (Vᗮ.starProjection ∘L U.starProjection)) =
    ContinuousLinearMap.modulus
      ((complexifySubmodule V)ᗮ.starProjection ∘L (complexifySubmodule U).starProjection)
  rw [complexify_modulus, complexify_comp,
    Submodule.starProjection_congr (complexifySubmodule_orthogonal V).symm,
    starProjection_complexifySubmodule, starProjection_complexifySubmodule]

/-- The same for the directed cosine. -/
@[simp] theorem complexify_directedCosAngleOperator :
    complexify (directedCosAngleOperator U V) = Real.directedCosAngleOperatorRC U V := by
  change complexify (ContinuousLinearMap.modulus (V.starProjection ∘L U.starProjection)) =
    ContinuousLinearMap.modulus
      ((complexifySubmodule V).starProjection ∘L (complexifySubmodule U).starProjection)
  rw [complexify_modulus, complexify_comp, starProjection_complexifySubmodule,
    starProjection_complexifySubmodule]

/-- The same for the directed `sin 2Θ₀`. -/
@[simp] theorem complexify_directedSinTwoAngleOperator :
    complexify (directedSinTwoAngleOperator U V) = Real.directedSinTwoAngleOperatorRC U V := by
  have hl : directedSinTwoAngleOperator U V =
      (2 : ℝ) • (directedSinAngleOperator U V * directedCosAngleOperator U V) := rfl
  have hmul : complexify (directedSinAngleOperator U V * directedCosAngleOperator U V) =
      complexify (directedSinAngleOperator U V) * complexify (directedCosAngleOperator U V) :=
    complexify_comp _ _
  rw [hl, complexify_real_smul, hmul, complexify_directedSinAngleOperator,
    complexify_directedCosAngleOperator]
  rfl

end DirectedReal

section DirectedTransport

variable {𝕂 : Type w} [RCLike 𝕂] {e : RCLikeIso 𝕜 𝕂}

open TauCeti.ScalarTransport

/-- The scalar transport carries the directed sine. -/
@[simp] theorem clm_directedSinAngleOperator :
    clm (e := e) (directedSinAngleOperator U V) =
      directedSinAngleOperator (ScalarTransport.submodule (e := e) U)
        (ScalarTransport.submodule (e := e) V) := by
  change clm (e := e) (ContinuousLinearMap.modulus (Vᗮ.starProjection ∘L U.starProjection)) =
    ContinuousLinearMap.modulus
      ((ScalarTransport.submodule (e := e) V)ᗮ.starProjection ∘L
        (ScalarTransport.submodule (e := e) U).starProjection)
  rw [clm_modulus,
    Submodule.starProjection_congr (ScalarTransport.submodule_orthogonal (e := e) V),
    starProjection_clm, starProjection_clm]
  rfl

/-- The scalar transport carries the directed cosine. -/
@[simp] theorem clm_directedCosAngleOperator :
    clm (e := e) (directedCosAngleOperator U V) =
      directedCosAngleOperator (ScalarTransport.submodule (e := e) U)
        (ScalarTransport.submodule (e := e) V) := by
  change clm (e := e) (ContinuousLinearMap.modulus (V.starProjection ∘L U.starProjection)) =
    ContinuousLinearMap.modulus
      ((ScalarTransport.submodule (e := e) V).starProjection ∘L
        (ScalarTransport.submodule (e := e) U).starProjection)
  rw [clm_modulus, starProjection_clm, starProjection_clm]
  rfl

/-- The scalar transport carries the directed `sin 2Θ₀`. -/
@[simp] theorem clm_directedSinTwoAngleOperator :
    clm (e := e) (directedSinTwoAngleOperator U V) =
      directedSinTwoAngleOperator (ScalarTransport.submodule (e := e) U)
        (ScalarTransport.submodule (e := e) V) := by
  have hl : directedSinTwoAngleOperator U V =
      (2 : ℝ) • (directedSinAngleOperator U V * directedCosAngleOperator U V) := rfl
  rw [hl, clm_real_smul, ScalarTransport.clm_mul, clm_directedSinAngleOperator,
    clm_directedCosAngleOperator]
  rfl

end DirectedTransport

section DirectedStructure

/-- The directed sine and cosine of a **real** pair commute, by descent from `ℂ`. -/
theorem commute_directedSinAngleOperator_directedCosAngleOperator_real {F : Type v}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] (U V : Submodule ℝ F)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    Commute (directedSinAngleOperator U V) (directedCosAngleOperator U V) := by
  refine complexify_injective ?_
  show complexify (directedSinAngleOperator U V ∘L directedCosAngleOperator U V) =
    complexify (directedCosAngleOperator U V ∘L directedSinAngleOperator U V)
  rw [complexify_comp, complexify_comp, complexify_directedSinAngleOperator,
    complexify_directedCosAngleOperator]
  exact commute_directedSinAngleOperatorC_directedCosAngleOperatorC _ _

/-- **The directed sine and cosine commute**, at an arbitrary `RCLike` field.  This is what
makes `2 sin Θ₀ cos Θ₀` the ordinary double-angle formula rather than a choice of ordering. -/
theorem commute_directedSinAngleOperator_directedCosAngleOperator :
    Commute (directedSinAngleOperator U V) (directedCosAngleOperator U V) := by
  have key : ∀ {𝕂 : Type} [RCLike 𝕂] (e : RCLikeIso 𝕜 𝕂),
      Commute (directedSinAngleOperator (TauCeti.ScalarTransport.submodule (e := e) U)
          (TauCeti.ScalarTransport.submodule (e := e) V))
        (directedCosAngleOperator (TauCeti.ScalarTransport.submodule (e := e) U)
          (TauCeti.ScalarTransport.submodule (e := e) V)) →
      Commute (directedSinAngleOperator U V) (directedCosAngleOperator U V) := by
    intro 𝕂 _ e h
    refine (TauCeti.ScalarTransport.clmEquiv (e := e)).injective ?_
    change TauCeti.ScalarTransport.clm (e := e)
        (directedSinAngleOperator U V * directedCosAngleOperator U V) =
      TauCeti.ScalarTransport.clm (e := e)
        (directedCosAngleOperator U V * directedSinAngleOperator U V)
    rw [TauCeti.ScalarTransport.clm_mul, TauCeti.ScalarTransport.clm_mul,
      clm_directedSinAngleOperator, clm_directedCosAngleOperator]
    exact h
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with h | h
  · exact key (RCLikeIso.real h)
      (commute_directedSinAngleOperator_directedCosAngleOperator_real _ _)
  · exact key (RCLikeIso.complex h)
      (commute_directedSinAngleOperatorC_directedCosAngleOperatorC _ _)

/-- The directed `sin 2Θ₀` is nonnegative: it is a nonnegative multiple of the product of two
commuting nonnegative operators. -/
theorem directedSinTwoAngleOperator_nonneg : 0 ≤ directedSinTwoAngleOperator U V := by
  have hprod : (0 : E →L[𝕜] E) ≤
      directedSinAngleOperator U V * directedCosAngleOperator U V :=
    (commute_iff_mul_nonneg (directedSinAngleOperator_nonneg U V)
      (directedCosAngleOperator_nonneg U V)).mp
      (commute_directedSinAngleOperator_directedCosAngleOperator U V)
  have hdef : directedSinTwoAngleOperator U V =
      (2 : ℝ) • (directedSinAngleOperator U V * directedCosAngleOperator U V) := rfl
  rw [hdef, two_smul]
  exact add_nonneg hprod hprod

/-- The directed `sin 2Θ₀` is self-adjoint. -/
theorem isSelfAdjoint_directedSinTwoAngleOperator :
    IsSelfAdjoint (directedSinTwoAngleOperator U V) := by
  have hdef : directedSinTwoAngleOperator U V =
      (2 : ℝ) • (directedSinAngleOperator U V * directedCosAngleOperator U V) := rfl
  have hmul : IsSelfAdjoint
      (directedSinAngleOperator U V * directedCosAngleOperator U V) := by
    rw [IsSelfAdjoint, star_mul, (isSelfAdjoint_directedCosAngleOperator U V).star_eq,
      (isSelfAdjoint_directedSinAngleOperator U V).star_eq]
    exact (commute_directedSinAngleOperator_directedCosAngleOperator U V).symm
  rw [hdef, two_smul]
  exact hmul.add hmul

end DirectedStructure


end Directed

/-! ## The reflection form of `sin 2Θ`

`sin 2Θ` is the modulus of the difference between the projection onto `U` and the projection
onto the mirror image of `U` through `V`.  This is the paper's own double-angle trick, and it
is the form every `sin 2Θ` estimate is actually proved in: the right-hand side is an ordinary
`sin Θ` between a reflected pair.

The identity holds at every `RCLike` field.  It is proved once over `ℂ`
(`directedSinTwoAngleOperatorC_eq_modulus_starProjection_sub`, a functional-calculus
computation), descended to `ℝ`, and then carried to an arbitrary field by the scalar
transport. -/

section ReflectionForm

/-- The projection onto a reflected complexified subspace is the complexification of the
projection onto the reflected real subspace. -/
theorem complexify_starProjection_map_reflection {F : Type v} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (U V : Submodule ℝ F)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    complexify ((U.map (V.reflection.toLinearEquiv : F →ₗ[ℝ] F)).starProjection -
        U.starProjection) =
      ((complexifySubmodule U).map
          ((complexifySubmodule V).reflection.toLinearEquiv :
            RealComplexification F →ₗ[ℂ] RealComplexification F)).starProjection -
        (complexifySubmodule U).starProjection := by
  have hconj : ∀ T : F →L[ℝ] F,
      _root_.TauCeti.DavisKahan.boundedUnitaryConjugate V.reflection T =
        V.reflectionOperator ∘L T ∘L V.reflectionOperator :=
    fun _ => ContinuousLinearMap.ext fun _ => rfl
  have hconjC : ∀ T : RealComplexification F →L[ℂ] RealComplexification F,
      _root_.TauCeti.DavisKahan.boundedUnitaryConjugate (complexifySubmodule V).reflection T =
        (complexifySubmodule V).reflectionOperator ∘L T ∘L
          (complexifySubmodule V).reflectionOperator :=
    fun _ => ContinuousLinearMap.ext fun _ => rfl
  have hrefl : complexify V.reflectionOperator = (complexifySubmodule V).reflectionOperator := by
    rw [Submodule.reflectionOperator_eq_two_smul_sub_id,
      Submodule.reflectionOperator_eq_two_smul_sub_id, complexify_sub,
      complexify_real_smul, complexify_id, starProjection_complexifySubmodule]
    norm_num
  rw [_root_.TauCeti.DavisKahan.starProjection_map_unitary U V.reflection,
    _root_.TauCeti.DavisKahan.starProjection_map_unitary (complexifySubmodule U)
      (complexifySubmodule V).reflection,
    complexify_sub, hconj U.starProjection,
    hconjC (complexifySubmodule U).starProjection,
    complexify_comp, complexify_comp, hrefl, starProjection_complexifySubmodule]

/-- The reflection form of `sin 2Θ` over `ℝ`, by descent from `ℂ`. -/
theorem sinTwoAngleOperatorR_eq_modulus_starProjection_sub {F : Type v} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] (U V : Submodule ℝ F)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    sinTwoAngleOperatorR U V =
      ((U.map (V.reflection.toLinearEquiv : F →ₗ[ℝ] F)).starProjection -
        U.starProjection).modulus := by
  refine complexify_injective ?_
  rw [complexify_sinTwoAngleOperatorR, complexify_modulus,
    complexify_starProjection_map_reflection,
    directedSinTwoAngleOperatorC_eq_modulus_starProjection_sub]

/-- Transport step: the reflection form at a field isomorphic to `𝕜` gives it at `𝕜`. -/
private theorem reflectionForm_of_transport {𝕂 : Type w} [RCLike 𝕂] (e : RCLikeIso 𝕜 𝕂)
    (h : sinTwoAngleOperator (TauCeti.ScalarTransport.submodule (e := e) U)
          (TauCeti.ScalarTransport.submodule (e := e) V) =
        (((TauCeti.ScalarTransport.submodule (e := e) U).map
              ((TauCeti.ScalarTransport.submodule (e := e) V).reflection.toLinearEquiv :
                TauCeti.ScalarTransport e E →ₗ[𝕂] TauCeti.ScalarTransport e E)).starProjection -
            (TauCeti.ScalarTransport.submodule (e := e) U).starProjection).modulus) :
    sinTwoAngleOperator U V =
      ((U.map (V.reflection.toLinearEquiv : E →ₗ[𝕜] E)).starProjection -
        U.starProjection).modulus := by
  refine (TauCeti.ScalarTransport.clmEquiv (e := e)).injective ?_
  change TauCeti.ScalarTransport.clm (e := e) (sinTwoAngleOperator U V) =
    TauCeti.ScalarTransport.clm (e := e) _
  rw [clm_sinTwoAngleOperator, TauCeti.ScalarTransport.clm_modulus,
    TauCeti.ScalarTransport.clm_sub, ← TauCeti.ScalarTransport.starProjection_clm,
    ← TauCeti.ScalarTransport.starProjection_clm,
    Submodule.starProjection_congr
      (TauCeti.ScalarTransport.submodule_map_reflection (e := e) U V)]
  exact h

/-- **The reflection form of `sin 2Θ`, at an arbitrary `RCLike` field.**

`sin 2Θ(U, V) = |P_{J_V U} - P_U|`, where `J_V` is the reflection in `V`.  This is what makes
a `sin 2Θ` bound an instance of a `sin Θ` bound for the reflected pair. -/
theorem sinTwoAngleOperator_eq_modulus_starProjection_sub :
    sinTwoAngleOperator U V =
      ((U.map (V.reflection.toLinearEquiv : E →ₗ[𝕜] E)).starProjection -
        U.starProjection).modulus := by
  rcases RCLike.I_eq_zero_or_im_I_eq_one (K := 𝕜) with h | h
  · refine reflectionForm_of_transport U V (RCLikeIso.real h) ?_
    rw [sinTwoAngleOperator_real]
    exact sinTwoAngleOperatorR_eq_modulus_starProjection_sub _ _
  · refine reflectionForm_of_transport U V (RCLikeIso.complex h) ?_
    rw [sinTwoAngleOperator_complex]
    exact directedSinTwoAngleOperatorC_eq_modulus_starProjection_sub _ _

/-- **An operator and its modulus have the same approximation numbers**, at an arbitrary
`RCLike` field.

`ContinuousLinearMap.modulus_hasSameApproximationNumbers` is stated over `ℂ` because the
modulus needs a real functional calculus on the operator algebra; this file activates that
calculus at every `RCLike` field, so the same one-line proof applies. -/
theorem modulus_hasSameApproximationNumbers_rclike {F : Type v} [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [CompleteSpace F] (T : E →L[𝕜] F) :
    (ContinuousLinearMap.modulus T).HasSameApproximationNumbers T :=
  ContinuousLinearMap.hasSameApproximationNumbers_of_norm_apply_eq _ _ T.norm_modulus_apply

/-- The consequence the ambient `sin 2Θ` theorem uses: `sin 2Θ` and the reflected projector
difference have the same complete singular-value sequence, so no unitarily invariant norm can
tell them apart. -/
theorem sinTwoAngleOperator_hasSameApproximationNumbers :
    (sinTwoAngleOperator U V).HasSameApproximationNumbers
      ((U.map (V.reflection.toLinearEquiv : E →ₗ[𝕜] E)).starProjection - U.starProjection) := by
  rw [sinTwoAngleOperator_eq_modulus_starProjection_sub]
  exact modulus_hasSameApproximationNumbers_rclike _

end ReflectionForm

/-! ## Order symmetry of the directed double-angle sine

`sin Θ₀(U, V)` and `sin Θ₀(V, U)` are genuinely different operators: a line inside a plane makes
the first zero and the second not.  Their *doubles* are not.  `sin 2Θ₀(U, V)` and
`sin 2Θ₀(V, U)` carry the same complete approximation-number sequence, so no unitarily
invariant norm distinguishes them.

This is the geometric fact the source-facing `sin 2Θ` wrapper needs.  The analytic estimate is
naturally parameterized by the pair (reducing subspace carrying the spectral gap, trial
subspace), whereas Davis and Kahan's `Θ₀` is the trial-side angle -- `‖Q^⊥P‖ = ‖sin Θ₀‖` with
`P` the trial projector and `Q` the one whose blocks are separated.  Without this theorem the
two sides of that correspondence are different operators and the wrapper would be stating a
different result.

The proof is one polar decomposition.  With `T = P_U P_V`,

`t = T T⋆ = P_U P_V P_U`,   `s = T⋆ T = P_V P_U P_V`,

both doubled sines are square roots -- `sin 2Θ₀(U,V)² = 4(t - t²)` and
`sin 2Θ₀(V,U)² = 4(s - s²)` -- and `W = T (1 - s)^{1/2}` has `W W⋆ = t - t²` and
`W⋆ W = s - s²`.  So the two are the moduli of `2W⋆` and `2W`, and an operator and its adjoint
have the same approximation numbers. -/

section Swap

omit [CompleteSpace E] in
/-- Orthogonal projections are idempotent, in the operator algebra. -/
private theorem starProjection_mul_self_generic (W : Submodule 𝕜 E)
    [W.HasOrthogonalProjection] :
    W.starProjection * W.starProjection = W.starProjection := by
  ext x
  show W.starProjection (W.starProjection x) = W.starProjection x
  rw [Submodule.starProjection_eq_self_iff]
  exact W.starProjection_apply_mem x

omit [CompleteSpace E] in
/-- Idempotence in the position a left-associated product actually presents it. -/
private theorem mul_starProjection_mul_self (W : Submodule 𝕜 E)
    [W.HasOrthogonalProjection] (x : E →L[𝕜] E) :
    x * W.starProjection * W.starProjection = x * W.starProjection := by
  rw [mul_assoc, starProjection_mul_self_generic]

omit [CompleteSpace E] in
/-- `P_{Wᗮ} = 1 - P_W`, in the operator algebra. -/
private theorem starProjection_orthogonal_generic (W : Submodule 𝕜 E)
    [W.HasOrthogonalProjection] :
    Wᗮ.starProjection = (1 : E →L[𝕜] E) - W.starProjection := by
  ext x
  simp

/-- The Gram operator of a cross projection product. -/
private theorem gram_cross_generic (U W : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [W.HasOrthogonalProjection] :
    (W.starProjection ∘L U.starProjection).adjoint ∘L
        (W.starProjection ∘L U.starProjection)
      = U.starProjection * W.starProjection * U.starProjection := by
  rw [ContinuousLinearMap.adjoint_comp, ← ContinuousLinearMap.star_eq_adjoint,
    ← ContinuousLinearMap.star_eq_adjoint, (isSelfAdjoint_starProjection U).star_eq,
    (isSelfAdjoint_starProjection W).star_eq]
  calc U.starProjection ∘L W.starProjection ∘L W.starProjection ∘L U.starProjection
      = U.starProjection * (W.starProjection * W.starProjection) * U.starProjection := by
        simp only [mul_assoc]; rfl
    _ = U.starProjection * W.starProjection * U.starProjection := by
        rw [starProjection_mul_self_generic]

/-- The square of the directed sine is the compressed cross block `P_U P_{Vᗮ} P_U`. -/
theorem directedSinAngleOperator_mul_self :
    directedSinAngleOperator U V * directedSinAngleOperator U V
      = U.starProjection * Vᗮ.starProjection * U.starProjection := by
  rw [directedSinAngleOperator, ContinuousLinearMap.modulus_mul_self]
  exact gram_cross_generic U Vᗮ

/-- The square of the directed cosine is the compressed cross block `P_U P_V P_U`. -/
theorem directedCosAngleOperator_mul_self :
    directedCosAngleOperator U V * directedCosAngleOperator U V
      = U.starProjection * V.starProjection * U.starProjection := by
  rw [directedCosAngleOperator, ContinuousLinearMap.modulus_mul_self]
  exact gram_cross_generic U V

/-- **The directed `sin 2Θ₀` squares to `4(t - t²)`**, where `t = P_U P_V P_U` is the
two-projection operator carrying the squared principal cosines. -/
theorem directedSinTwoAngleOperator_mul_self :
    directedSinTwoAngleOperator U V * directedSinTwoAngleOperator U V
      = (4 : ℝ) • (U.starProjection * V.starProjection * U.starProjection -
          U.starProjection * V.starProjection * U.starProjection *
            (U.starProjection * V.starProjection * U.starProjection)) := by
  have hAA : U.starProjection * U.starProjection = U.starProjection :=
    starProjection_mul_self_generic U
  have hcomm := commute_directedSinAngleOperator_directedCosAngleOperator U V
  have hsin : directedSinAngleOperator U V * directedSinAngleOperator U V
      = U.starProjection - U.starProjection * V.starProjection * U.starProjection := by
    rw [directedSinAngleOperator_mul_self, starProjection_orthogonal_generic, mul_sub, sub_mul,
      mul_one, hAA]
  have hcos := directedCosAngleOperator_mul_self U V
  have hrearrange :
      directedSinAngleOperator U V * directedCosAngleOperator U V *
          (directedSinAngleOperator U V * directedCosAngleOperator U V)
        = (directedSinAngleOperator U V * directedSinAngleOperator U V) *
            (directedCosAngleOperator U V * directedCosAngleOperator U V) := by
    calc directedSinAngleOperator U V * directedCosAngleOperator U V *
          (directedSinAngleOperator U V * directedCosAngleOperator U V)
        = directedSinAngleOperator U V *
            (directedCosAngleOperator U V * directedSinAngleOperator U V) *
              directedCosAngleOperator U V := by noncomm_ring
      _ = directedSinAngleOperator U V *
            (directedSinAngleOperator U V * directedCosAngleOperator U V) *
              directedCosAngleOperator U V := by rw [hcomm.symm.eq]
      _ = (directedSinAngleOperator U V * directedSinAngleOperator U V) *
            (directedCosAngleOperator U V * directedCosAngleOperator U V) := by noncomm_ring
  show (2 : ℝ) • _ * ((2 : ℝ) • _) = _
  rw [smul_mul_smul_comm, hrearrange, hsin, hcos]
  congr 1
  · norm_num
  · simp only [sub_mul, ← mul_assoc, mul_starProjection_mul_self,
      starProjection_mul_self_generic]

/-- **The directed double-angle sine is order-symmetric at the level of approximation
numbers.**

`sin 2Θ₀(U, V)` and `sin 2Θ₀(V, U)` have the same complete approximation-number sequence, so no
unitarily invariant norm distinguishes them.  The individual directed sines do *not* have this
property -- a line inside a plane makes `sin Θ₀(U, V)` zero and `sin Θ₀(V, U)` not -- so this
is a fact about the doubling, and it needs a proof.

`sin 2Θ₀(U,V)² = 4(t - t²)` and `sin 2Θ₀(V,U)² = 4(s - s²)` for the two Gram operators
`t = T T⋆` and `s = T⋆ T` of the single operator `T = P_U P_V`.  So with `W = T (1 - s)^{1/2}`
the two are the moduli of `2W⋆` and `2W`, which have the same approximation numbers. -/
theorem directedSinTwoAngleOperator_hasSameApproximationNumbers_swap :
    (directedSinTwoAngleOperator U V).HasSameApproximationNumbers
      (directedSinTwoAngleOperator V U) := by
  have hAsa : star U.starProjection = U.starProjection :=
    (isSelfAdjoint_starProjection U).star_eq
  have hBsa : star V.starProjection = V.starProjection :=
    (isSelfAdjoint_starProjection V).star_eq
  set T : E →L[𝕜] E := U.starProjection * V.starProjection with hTdef
  have hTstar : star T = V.starProjection * U.starProjection := by
    rw [hTdef, star_mul, hAsa, hBsa]
  set t : E →L[𝕜] E := U.starProjection * V.starProjection * U.starProjection with htdef
  set s : E →L[𝕜] E := V.starProjection * U.starProjection * V.starProjection with hsdef
  have htT : T * star T = t := by
    rw [hTdef, hTstar, htdef]
    simp only [← mul_assoc, mul_starProjection_mul_self]
  have hsT : star T * T = s := by
    rw [hTdef, hTstar, hsdef]
    simp only [← mul_assoc, mul_starProjection_mul_self]
  -- `1 - s` splits as `P_{Vᗮ} + (P_{Uᗮ} P_V)⋆ (P_{Uᗮ} P_V)`, so it is nonnegative.
  have hnn : (0 : E →L[𝕜] E) ≤ 1 - s := by
    have hVo : star Vᗮ.starProjection * Vᗮ.starProjection
        = (1 : E →L[𝕜] E) - V.starProjection := by
      rw [(isSelfAdjoint_starProjection Vᗮ).star_eq, starProjection_mul_self_generic,
        starProjection_orthogonal_generic]
    have hUo : star (Uᗮ.starProjection * V.starProjection) *
        (Uᗮ.starProjection * V.starProjection) = V.starProjection - s := by
      rw [star_mul, (isSelfAdjoint_starProjection Uᗮ).star_eq, hBsa]
      simp only [← mul_assoc, mul_starProjection_mul_self]
      rw [starProjection_orthogonal_generic U, hsdef, mul_sub, sub_mul, mul_one,
        starProjection_mul_self_generic]
    have hsum : (1 : E →L[𝕜] E) - s
        = star Vᗮ.starProjection * Vᗮ.starProjection
          + star (Uᗮ.starProjection * V.starProjection) *
              (Uᗮ.starProjection * V.starProjection) := by
      rw [hVo, hUo]; abel
    rw [hsum]
    exact add_nonneg (star_mul_self_nonneg _) (star_mul_self_nonneg _)
  set S : E →L[𝕜] E := CFC.sqrt (1 - s) with hSdef
  have hSS : S * S = 1 - s := CFC.sqrt_mul_sqrt_self _ hnn
  have hSsa : star S = S :=
    (IsSelfAdjoint.of_nonneg (hSdef ▸ CFC.sqrt_nonneg (1 - s))).star_eq
  have hs' : s = 1 - S * S := by rw [hSS]; abel
  set W : E →L[𝕜] E := T * S with hWdef
  have hWstar : star W = S * star T := by rw [hWdef, star_mul, hSsa]
  have hWW : W * star W = t - t * t := by
    have h1 : W * star W = T * (S * S) * star T := by
      rw [hWdef, hWstar]; noncomm_ring
    have h2 : T * (1 - star T * T) * star T
        = T * star T - T * star T * (T * star T) := by noncomm_ring
    rw [h1, hSS, ← hsT, h2, htT]
  have hW'W : star W * W = s - s * s := by
    have h1 : star W * W = S * (star T * T) * S := by
      rw [hWdef, hWstar]; noncomm_ring
    rw [h1, hsT, hs']
    noncomm_ring
  have hstar2 : ∀ x : E →L[𝕜] E, star ((2 : ℝ) • x) = (2 : ℝ) • star x := by
    intro x; rw [two_smul, two_smul, star_add]
  have hfour : ∀ a b : E →L[𝕜] E,
      ((2 : ℝ) • a) * ((2 : ℝ) • b) = (4 : ℝ) • (a * b) := by
    intro a b
    rw [smul_mul_smul_comm]
    norm_num
  have hUV : directedSinTwoAngleOperator U V
      = ContinuousLinearMap.modulus ((2 : ℝ) • star W) := by
    refine ContinuousLinearMap.eq_modulus_of_nonneg_of_mul_self_eq
      (directedSinTwoAngleOperator_nonneg U V) ?_
    show _ = star ((2 : ℝ) • star W) * ((2 : ℝ) • star W)
    rw [hstar2, star_star, hfour, hWW, directedSinTwoAngleOperator_mul_self, ← htdef]
  have hVU : directedSinTwoAngleOperator V U
      = ContinuousLinearMap.modulus ((2 : ℝ) • W) := by
    refine ContinuousLinearMap.eq_modulus_of_nonneg_of_mul_self_eq
      (directedSinTwoAngleOperator_nonneg V U) ?_
    show _ = star ((2 : ℝ) • W) * ((2 : ℝ) • W)
    rw [hstar2, hfour, hW'W, directedSinTwoAngleOperator_mul_self, ← hsdef]
  intro n
  rw [hUV, hVU, modulus_hasSameApproximationNumbers_rclike ((2 : ℝ) • star W) n,
    modulus_hasSameApproximationNumbers_rclike ((2 : ℝ) • W) n,
    show ((2 : ℝ) • star W) = ((2 : ℝ) • W).adjoint by
      rw [← ContinuousLinearMap.star_eq_adjoint, hstar2],
    ContinuousLinearMap.approximationNumber_adjoint]

end Swap


end

end DavisKahan.Angle
end TauCeti
