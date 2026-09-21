/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.RCLike.ScalarTransportFunctionalCalculus
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# The modulus of a Hilbert-space operator

For a bounded operator `T : E →L[𝕜] F` between Hilbert spaces over `𝕜 : RCLike`, its
**modulus** `|T| = (T⋆ T)^(1/2)` is the positive square root, through the
continuous functional calculus, of the Gram operator `T⋆ T` acting on the
*source* space `E`.

The definition is stated for a general (rectangular) `T`: the source space
alone determines the construction, and the endomorphism case `F = E` is a
specialization rather than a separate definition (`modulus_eq_sqrt_star_mul_self`,
`modulus_mul_self_eq_star_mul_self`).

## Scalar infrastructure

`CFC.sqrt` is a statement about the real algebra `E →L[𝕜] E`.  For an arbitrary
`RCLike 𝕜`, the required real algebra, scalar tower, and real self-adjoint continuous
functional calculus are canonical constructions in `ForTauCeti`.  They are activated here
as low-priority local instances.  They are intentionally not global instances: making the
extra real scalar action globally visible changes elaboration of scalar multiplication in
unrelated operator proofs.

Consequently the public modulus API below has only the mathematical Hilbert-space and
completeness assumptions.  Callers do not supply `Algebra ℝ (E →L[𝕜] E)`,
`IsScalarTower ℝ 𝕜 (E →L[𝕜] E)`, or a continuous-functional-calculus instance.

**Its finite-dimensional counterpart.** `TauCeti.operatorAbs` in
`ForTauCeti/Analysis/InnerProductSpace/Polar/Decomposition.lean` is the finite-dimensional
`RCLike` modulus, built from the spectral square root rather than from the continuous functional
calculus.  It is rectangular as well: for `A : E →ₗ[𝕜] F`, `operatorAbs A` acts on the source
`E`.  `Polar/CFCBridge.lean` proves that its bounded realization agrees with `modulus`.

## Main results

* `ContinuousLinearMap.modulus_mul_self`: the defining identity
  `|T| * |T| = T⋆ T`;
* `ContinuousLinearMap.eq_modulus_of_nonneg_of_mul_self_eq`: `|T|` is the
  *unique* nonnegative square root of the Gram operator;
* `ContinuousLinearMap.norm_modulus_apply`: the pointwise isometry
  `‖|T| x‖ = ‖T x‖`, from which `ContinuousLinearMap.norm_modulus`
  (`‖|T|‖ = ‖T‖`) and the one-sided composition laws
  `ContinuousLinearMap.norm_modulus_comp` (`‖|T| ∘L D‖ = ‖T ∘L D‖`) and
  `ContinuousLinearMap.norm_comp_modulus` (`‖D ∘L |T|‖ = ‖D ∘L T⋆‖`) follow;
* `ContinuousLinearMap.modulus_apply_eq_zero_iff`: `|T| x = 0 ↔ T x = 0`;
* `ContinuousLinearMap.modulus_commute_modulus`: moduli of operators with
  commuting Gram operators commute.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original modules: `DavisKahan/OperatorIdeal/ApproximationNumbers/OperatorModulus.lean`
  (`rectangularOperatorModulus` and its API, Jon Crall / OpenAI GPT-5.6 Thinking)
  and `ForMathlib/Analysis/InnerProductSpace/OperatorAbsoluteValue.lean`
  (`operatorAbs` and its API, Jon Crall / Claude Fable 5), both at Davis--Kahan
  commit `fc38eb4`; Apache 2.0.
* Extraction class: **unified and generalized**.  Per the signature-polish
  backlog, the two parallel APIs —
  one rectangular, one square — are replaced by this single rectangular
  definition with dot notation on `ContinuousLinearMap`.  The square-only
  composition laws `norm_operatorAbs_mul` / `norm_mul_operatorAbs` are
  generalized to rectangular operators here, and reproved from the pointwise
  isometry instead of the C⋆-identity; the uniqueness and commutation results
  are likewise generalized.
* Spectra influence: **none** — the construction uses Mathlib together with the reusable
  `ForTauCeti` scalar-transport functional calculus.
-/

public section

namespace ContinuousLinearMap

open scoped InnerProductSpace

universe u v w

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} {F : Type v} {G : Type w}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]

/-- The Gram operator `T⋆ T` is nonnegative.  This is the `0 ≤ ·` form of
`ContinuousLinearMap.isPositive_adjoint_comp_self`. -/
theorem adjoint_comp_self_nonneg (T : E →L[𝕜] F) : 0 ≤ T.adjoint ∘L T :=
  (nonneg_iff_isPositive (f := _)).mpr (isPositive_adjoint_comp_self T)

omit [CompleteSpace E] [CompleteSpace F] [CompleteSpace G] in
/-- Two operators out of the same space with pointwise equal norms have equal
operator norms.  Local scaffolding for the modulus norm laws. -/
private theorem opNorm_eq_of_forall_norm_apply_eq {f : E →L[𝕜] F} {g : E →L[𝕜] G}
    (h : ∀ x, ‖f x‖ = ‖g x‖) : ‖f‖ = ‖g‖ :=
  le_antisymm
    (f.opNorm_le_bound (norm_nonneg g) fun x => (h x).trans_le (g.le_opNorm x))
    (g.opNorm_le_bound (norm_nonneg f) fun x => (h x).symm.trans_le (f.le_opNorm x))

/-! ### Local scalar and functional-calculus instances -/

attribute [local instance 100] ContinuousLinearMap.realAlgebra
  ContinuousLinearMap.realIsScalarTower ContinuousLinearMap.continuousFunctionalCalculusReal
  ContinuousLinearMap.instStarOrderedRingRCLike

/-- The modulus `|T| = (T⋆ T)^(1/2)` of a bounded operator between Hilbert
spaces: the positive square root, through the continuous functional
calculus, of the Gram operator `T⋆ T` on the source space. -/
noncomputable def modulus (T : E →L[𝕜] F) : E →L[𝕜] E :=
  CFC.sqrt (T.adjoint ∘L T)

/-- **The modulus unfolded.**  The characteristic lemma: `|T|` is the functional
calculus square root of the Gram operator.  A consumer in another module that
needs to rewrite through the definition should use this rather than `rw
[modulus]`, which only works while the body is exposed.

`modulus_eq_sqrt_star_mul_self` is the endomorphism specialization, in
C⋆-algebra notation. -/
theorem modulus_def (T : E →L[𝕜] F) : T.modulus = CFC.sqrt (T.adjoint ∘L T) := (rfl)

/-- The modulus is insensitive to multiplication by `-1`. -/
@[simp]
theorem modulus_neg (T : E →L[𝕜] F) : (-T).modulus = T.modulus := by
  rw [modulus_def, modulus_def]
  congr 1
  ext x
  simp only [ContinuousLinearMap.comp_apply, map_neg, neg_apply,
    neg_neg]

/-- The modulus is nonnegative in the C⋆-order. -/
theorem modulus_nonneg (T : E →L[𝕜] F) : 0 ≤ T.modulus :=
  CFC.sqrt_nonneg _

/-- The modulus is self-adjoint. -/
theorem modulus_isSelfAdjoint (T : E →L[𝕜] F) : IsSelfAdjoint T.modulus :=
  .of_nonneg T.modulus_nonneg

/-- The modulus is self-adjoint, being a positive square root. -/
@[simp]
theorem adjoint_modulus (T : E →L[𝕜] F) : T.modulus.adjoint = T.modulus := by
  rw [← star_eq_adjoint]
  exact T.modulus_isSelfAdjoint.star_eq

/-- The defining identity `|T| * |T| = T⋆ T`. -/
theorem modulus_mul_self (T : E →L[𝕜] F) :
    T.modulus * T.modulus = T.adjoint ∘L T :=
  CFC.sqrt_mul_sqrt_self _ T.adjoint_comp_self_nonneg

/-- The modulus is the *unique* nonnegative square root of the Gram
operator. -/
theorem eq_modulus_of_nonneg_of_mul_self_eq {T : E →L[𝕜] F} {b : E →L[𝕜] E}
    (hb : 0 ≤ b) (h : b * b = T.adjoint ∘L T) : b = T.modulus :=
  (CFC.sqrt_unique h hb).symm

/-- The modulus is a pointwise isometry onto the values of `T`:
`‖|T| x‖ = ‖T x‖`.  This is the computational heart of the modulus API — the
operator-norm and composition laws below all reduce to it. -/
@[simp]
theorem norm_modulus_apply (T : E →L[𝕜] F) (x : E) : ‖T.modulus x‖ = ‖T x‖ := by
  have hinner : (⟪T.modulus x, T.modulus x⟫_𝕜 : 𝕜) = ⟪T x, T x⟫_𝕜 := by
    calc (⟪T.modulus x, T.modulus x⟫_𝕜 : 𝕜)
        = ⟪T.modulus.adjoint x, T.modulus x⟫_𝕜 := by rw [adjoint_modulus]
      _ = ⟪x, T.modulus (T.modulus x)⟫_𝕜 := adjoint_inner_left _ _ _
      _ = ⟪x, (T.modulus * T.modulus) x⟫_𝕜 := (rfl)
      _ = ⟪x, (T.adjoint ∘L T) x⟫_𝕜 := by rw [modulus_mul_self]
      _ = ⟪T x, T x⟫_𝕜 := adjoint_inner_right T x (T x)
  have hsq : ‖T.modulus x‖ ^ 2 = ‖T x‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hinner
    exact_mod_cast hinner
  have hsqrt := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hsqrt

/-- The modulus vanishes exactly where the operator does.

Immediate from `norm_modulus_apply`, but worth its own name: it is how the
directed angle operators are shown to vanish off the source subspace. -/
@[simp]
theorem modulus_apply_eq_zero_iff (T : E →L[𝕜] F) (x : E) :
    T.modulus x = 0 ↔ T x = 0 := by
  rw [← norm_eq_zero, ← norm_eq_zero (a := T x), norm_modulus_apply]

/-- The modulus has the same operator norm as the original map. -/
@[simp]
theorem norm_modulus (T : E →L[𝕜] F) : ‖T.modulus‖ = ‖T‖ :=
  opNorm_eq_of_forall_norm_apply_eq T.norm_modulus_apply

omit [CompleteSpace G] in
/-- Precomposition sees only the modulus: `‖|T| ∘L D‖ = ‖T ∘L D‖`, since the
two composites agree pointwise in norm. -/
theorem norm_modulus_comp (T : E →L[𝕜] F) (D : G →L[𝕜] E) :
    ‖T.modulus ∘L D‖ = ‖T ∘L D‖ :=
  opNorm_eq_of_forall_norm_apply_eq fun x => T.norm_modulus_apply (D x)

/-- Postcomposition sees the modulus as the adjoint: `‖D ∘L |T|‖ = ‖D ∘L T⋆‖`.

The two sides act on different spaces (`|T|` lives on the source of `T`, `T⋆`
on its target); the identity is between their operator norms, obtained by
conjugating `norm_modulus_comp` with the isometric adjoint. -/
theorem norm_comp_modulus (D : E →L[𝕜] G) (T : E →L[𝕜] F) :
    ‖D ∘L T.modulus‖ = ‖D ∘L T.adjoint‖ := by
  calc ‖D ∘L T.modulus‖
      = ‖(D ∘L T.modulus).adjoint‖ := (LinearIsometryEquiv.norm_map adjoint _).symm
    _ = ‖T.modulus ∘L D.adjoint‖ := by rw [adjoint_comp, adjoint_modulus]
    _ = ‖T ∘L D.adjoint‖ := T.norm_modulus_comp D.adjoint
    _ = ‖(T ∘L D.adjoint).adjoint‖ := (LinearIsometryEquiv.norm_map adjoint _).symm
    _ = ‖D ∘L T.adjoint‖ := by rw [adjoint_comp, adjoint_adjoint]

/-- Anything commuting with the Gram operator `T†T` commutes with `T.modulus`. -/
theorem commute_modulus_of_commute_gram {T : E →L[𝕜] F} {b : E →L[𝕜] E}
    (h : Commute (T.adjoint ∘L T) b) : Commute T.modulus b := by
  rw [modulus, CFC.sqrt]
  exact Commute.cfcₙ_nnreal h NNReal.sqrt

/-- Moduli of operators whose Gram operators commute themselves commute.  The
two operators may have different targets: both moduli act on the common source
space. -/
theorem modulus_commute_modulus {S : E →L[𝕜] F} {T : E →L[𝕜] G}
    (h : Commute (S.adjoint ∘L S) (T.adjoint ∘L T)) :
    Commute S.modulus T.modulus := by
  have h1 : Commute (CFC.sqrt (S.adjoint ∘L S)) (T.adjoint ∘L T) :=
    Commute.cfcₙ_nnreal h _
  have h2 : Commute (CFC.sqrt (T.adjoint ∘L T)) (CFC.sqrt (S.adjoint ∘L S)) :=
    Commute.cfcₙ_nnreal h1.symm _
  exact h2.symm

/-! ### The endomorphism case

For `T : E →L[𝕜] E` the Gram operator is the C⋆-algebra element `star T * T`,
so the modulus is the absolute value of `T` in the C⋆-algebra `E →L[𝕜] E`.
These are specializations of the definition above, not a second construction. -/

/-- Anything commuting with `star T * T` commutes with the modulus of the endomorphism `T`. -/
theorem commute_modulus_of_commute_star_mul_self (T b : E →L[𝕜] E)
    (h : Commute (star T * T) b) : Commute T.modulus b := by
  apply commute_modulus_of_commute_gram
  simpa [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def] using h

/-- On an endomorphism the modulus is the C⋆-algebra absolute value. -/
theorem modulus_eq_sqrt_star_mul_self (T : E →L[𝕜] E) :
    T.modulus = CFC.sqrt (star T * T) := (rfl)
/-- The defining identity in C⋆-algebra form. -/
theorem modulus_mul_self_eq_star_mul_self (T : E →L[𝕜] E) :
    T.modulus * T.modulus = star T * T :=
  T.modulus_mul_self

end ContinuousLinearMap

end
