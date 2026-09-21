/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/

/-
Staged for Tau Ceti: pinching contracts every Ky Fan approximation gauge.
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.Core
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks

/-!
# Pinching contracts Ky Fan approximation gauges

Discarding the off-diagonal blocks of an operator relative to an orthogonal
decomposition `E = U ⊕ Uᗮ` cannot increase any Ky Fan sum of its approximation
numbers:

```
∑_{n<k} aₙ(P_U A P_U + P_Uᗮ A P_Uᗮ)  ≤  ∑_{n<k} aₙ(A).
```

This is the Fan--Hoffman pinching contraction at approximation-number scope,
which is what an arbitrary unitarily invariant ideal gauge sees through Fan
dominance.  In the Davis--Kahan development it is the step that turns a
statement about the two *restricted* displacements into one about the full
displacement — Proposition 4.3's route.

## Why it is three lines

The pinch is an average of two unitary conjugations.  `Submodule.reflectionOperator`
`J = 2P_U − 1` is a self-adjoint unitary, and

```
2 (P_U A P_U + P_Uᗮ A P_Uᗮ) = A + J A J
```

(`Submodule.two_smul_diagonalPart_eq_add_reflectionConjugate`).  Conjugating by a
contraction cannot increase a Ky Fan gauge, and the gauge is subadditive, so the
average is dominated.  No majorization theory is needed at this level: the
majorization content is already inside subadditivity of the gauge.

The scalar field is `ℂ` because the unconditional Ky Fan triangle inequality is
available there (`kyFanApproximationGauge_add_le_complex`); over a general
`RCLike` field the same proof runs given
`ContinuousLinearMap.HasMinMaxLowerBoundEverywhere`.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`; it has had no prior home.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and
  `ForTauCeti`.
-/

public section

namespace TauCeti
namespace ApproximationNumber

open scoped InnerProductSpace

universe v

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- **Conjugating by a reflection preserves Ky Fan approximation gauges.**

A reflection is a contraction in both slots, so the gauge cannot grow; it is
also involutive, so it cannot shrink either.  Only the `≤` direction is used
below, but the equality is the honest statement. -/
theorem kyFanApproximationGauge_reflectionConjugate_le
    (U : Submodule ℂ E) [U.HasOrthogonalProjection] (A : E →L[ℂ] E) (k : ℕ) :
    kyFanApproximationGauge k
        (U.reflectionOperator ∘L A ∘L U.reflectionOperator) ≤
      kyFanApproximationGauge k A := by
  have h := kyFanApproximationGauge_comp_le (𝕜 := ℂ) k
    U.reflectionOperator A U.reflectionOperator
  have hJ : ‖(U.reflectionOperator : E →L[ℂ] E)‖ ≤ 1 :=
    Submodule.norm_reflectionOperator_le_one U
  have hnn : 0 ≤ kyFanApproximationGauge k A :=
    kyFanApproximationGauge_nonneg k A
  refine h.trans ?_
  have h1 : ‖(U.reflectionOperator : E →L[ℂ] E)‖ *
      kyFanApproximationGauge k A ≤ 1 * kyFanApproximationGauge k A :=
    mul_le_mul_of_nonneg_right hJ hnn
  calc
    ‖(U.reflectionOperator : E →L[ℂ] E)‖ * kyFanApproximationGauge k A *
        ‖(U.reflectionOperator : E →L[ℂ] E)‖ ≤
        1 * kyFanApproximationGauge k A * 1 :=
      mul_le_mul h1 hJ (norm_nonneg _) (by linarith)
    _ = kyFanApproximationGauge k A := by ring

omit [CompleteSpace E] in
/-- **Conjugating by a contraction pair cannot increase a Ky Fan approximation gauge.**

The two-sided ideal inequality with both norms at most one.  Stated for a bare pair of
contractions rather than for an isometry equivalence, so that the equality below can apply
it twice with the roles exchanged. -/
theorem kyFanApproximationGauge_conj_le_complex {F : Type v} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] {L : E →L[ℂ] F} {R : F →L[ℂ] E}
    (hL : ‖L‖ ≤ 1) (hR : ‖R‖ ≤ 1) (A : E →L[ℂ] E) (k : ℕ) :
    kyFanApproximationGauge k (L ∘L A ∘L R) ≤ kyFanApproximationGauge k A := by
  refine (kyFanApproximationGauge_comp_le (𝕜 := ℂ) k L A R).trans ?_
  have hnn : 0 ≤ kyFanApproximationGauge k A := kyFanApproximationGauge_nonneg k A
  have h1 : ‖L‖ * kyFanApproximationGauge k A ≤ 1 * kyFanApproximationGauge k A :=
    mul_le_mul_of_nonneg_right hL hnn
  calc
    ‖L‖ * kyFanApproximationGauge k A * ‖R‖ ≤ 1 * kyFanApproximationGauge k A * 1 :=
      mul_le_mul h1 hR (norm_nonneg _) (by linarith)
    _ = kyFanApproximationGauge k A := by ring

/-- **Ky Fan approximation gauges are invariant under conjugation by an isometry
equivalence**, in the form the block chart needs: a contraction pair with `R ∘L L = 1`.

Only the one-sided hypothesis `R ∘L L = 1` is used.  The `≤` direction is
`kyFanApproximationGauge_conj_le_complex`; the `≥` direction is the *same* lemma with `L` and `R`
exchanged, applied to `L ∘L A ∘L R`, since `R ∘L (L ∘L A ∘L R) ∘L L = A`.  Proving it once
and applying it twice is what keeps this off a self-referential rewrite. -/
theorem kyFanApproximationGauge_conj_eq_complex {F : Type v} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] {L : E →L[ℂ] F} {R : F →L[ℂ] E}
    (hL : ‖L‖ ≤ 1) (hR : ‖R‖ ≤ 1) (hRL : R ∘L L = ContinuousLinearMap.id ℂ E)
    (A : E →L[ℂ] E) (k : ℕ) :
    kyFanApproximationGauge k (L ∘L A ∘L R) = kyFanApproximationGauge k A := by
  refine le_antisymm (kyFanApproximationGauge_conj_le_complex hL hR A k) ?_
  have hRLapp : ∀ y : E, R (L y) = y := by
    intro y
    have h := congrArg (fun T : E →L[ℂ] E => T y) hRL
    simpa using h
  have hcomp : R ∘L (L ∘L A ∘L R) ∘L L = A := by
    ext x
    simp only [ContinuousLinearMap.comp_apply]
    rw [hRLapp x, hRLapp (A x)]
  have h := kyFanApproximationGauge_conj_le_complex hR hL (L ∘L A ∘L R) k
  rwa [hcomp] at h

/-- **Pinching contracts every Ky Fan approximation gauge.**

`∑_{n<k} aₙ(P_U A P_U + P_Uᗮ A P_Uᗮ) ≤ ∑_{n<k} aₙ(A)`.

The pinch is the average of `A` and its reflection conjugate, and the gauge is
subadditive and conjugation-invariant. -/
theorem kyFanApproximationGauge_diagonalPart_le_complex
    (U : Submodule ℂ E) [U.HasOrthogonalProjection] (A : E →L[ℂ] E) (k : ℕ) :
    kyFanApproximationGauge k (U.diagonalPart A) ≤
      kyFanApproximationGauge k A := by
  have hsplit := Submodule.two_smul_diagonalPart_eq_add_reflectionConjugate
    (𝕜 := ℂ) U A
  have hsum : kyFanApproximationGauge k ((2 : ℂ) • U.diagonalPart A) ≤
      2 * kyFanApproximationGauge k A := by
    rw [hsplit]
    refine (kyFanApproximationGauge_add_le_complex k A
      (U.reflectionOperator ∘L A ∘L U.reflectionOperator)).trans ?_
    have := kyFanApproximationGauge_reflectionConjugate_le U A k
    linarith
  rw [kyFanApproximationGauge_smul] at hsum
  have hnorm : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [hnorm] at hsum
  linarith

end ApproximationNumber
end TauCeti
