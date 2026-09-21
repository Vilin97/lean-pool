/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Index
import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.Herbrand
/-!
# The final cardinal step in the idele-class Herbrand calculation

This file isolates the final cardinality argument in the idele-class Herbrand calculation. The
Herbrand quotients of the supported ideles and of the corresponding
principal ideles have a common nonzero local-degree factor.  Cancelling
that factor in the exact-sequence identity gives

`h(G, C_L) = |G|`.

The degree-zero Tate group is the actual idele-class norm quotient, so
its cardinality, and hence the norm index, is at least `|G| = [L : K]`.
-/

open scoped NumberField
open NumberField

noncomputable section

open RelativeIdeleGroup.Cohomology


open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology

variable
    (K L : Type) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- Finiteness of the two low Tate groups of the actual relative idele
module, with its concrete Galois action. -/
def RelativeIdeleHerbrandQuotientDefined
    (σ : L ≃ₐ[K] L) : Prop :=
  letI := relativeIdeleMulDistribMulAction K L
  HerbrandQuotientDefined
    (L ≃ₐ[K] L) (RelativeIdeleGroup K L) σ

/-- Finiteness of the two low Tate groups of the actual principal-idele
module, with its concrete restricted Galois action. -/
def PrincipalIdeleHerbrandQuotientDefined
    (σ : L ≃ₐ[K] L) : Prop :=
  letI := relativeIdeleMulDistribMulAction K L
  letI := principalIdeleMulDistribMulAction K L
  HerbrandQuotientDefined
    (L ≃ₐ[K] L)
    (RelativeIdeleGroup.principalSubgroup K L) σ

omit [NumberField L] [IsGalois K L] in
/-- Cancellation for the final idele-class Herbrand quotient.  If the relative-idele and
principal-idele Herbrand quotients are respectively `q` and
`q / |G|`, then the idele-class Herbrand quotient is `|G|`.

The hypotheses are phrased on the actual relative idele and principal
idele groups.  The preceding supported-idele calculation supplies these
four finiteness instances and the two displayed values. -/
theorem ideleClass_herbrandQuotient_eq_card_of_relative_principal_values
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ)
    (hRelativeDefined :
      RelativeIdeleHerbrandQuotientDefined K L σ)
    (hPrincipalDefined :
      PrincipalIdeleHerbrandQuotientDefined K L σ)
    (q : ℚ) (hq : q ≠ 0)
    (hRelative :
      letI := relativeIdeleMulDistribMulAction K L
      letI : Finite
          (HerbrandH0 (L ≃ₐ[K] L)
            (RelativeIdeleGroup K L)) :=
        hRelativeDefined.1
      letI : Finite
          (HerbrandHMinusOne (L ≃ₐ[K] L)
            (RelativeIdeleGroup K L) σ) :=
        hRelativeDefined.2
      herbrandQuotient
          (G := L ≃ₐ[K] L)
          (A := RelativeIdeleGroup K L) σ = q)
    (hPrincipal :
      letI := relativeIdeleMulDistribMulAction K L
      letI := principalIdeleMulDistribMulAction K L
      letI : Finite
          (HerbrandH0 (L ≃ₐ[K] L)
            (RelativeIdeleGroup.principalSubgroup K L)) :=
        hPrincipalDefined.1
      letI : Finite
          (HerbrandHMinusOne (L ≃ₐ[K] L)
            (RelativeIdeleGroup.principalSubgroup K L) σ) :=
        hPrincipalDefined.2
      herbrandQuotient
          (G := L ≃ₐ[K] L)
          (A := RelativeIdeleGroup.principalSubgroup K L) σ =
        q / (Fintype.card (L ≃ₐ[K] L) : ℚ)) :
    letI := ideleClassMulDistribMulAction K L
    ∃ hC :
        HerbrandQuotientDefined
          (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L) σ,
      @herbrandQuotient
          (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L)
          _ _ _ _ σ hC.1 hC.2 =
        (Fintype.card (L ≃ₐ[K] L) : ℚ) := by
  let := relativeIdeleMulDistribMulAction K L
  let := principalIdeleMulDistribMulAction K L
  let := ideleClassMulDistribMulAction K L
  let : Finite
      (HerbrandH0 (L ≃ₐ[K] L)
        (RelativeIdeleGroup K L)) :=
    hRelativeDefined.1
  let : Finite
      (HerbrandHMinusOne (L ≃ₐ[K] L)
        (RelativeIdeleGroup K L) σ) :=
    hRelativeDefined.2
  let : Finite
      (HerbrandH0 (L ≃ₐ[K] L)
        (RelativeIdeleGroup.principalSubgroup K L)) :=
    hPrincipalDefined.1
  let : Finite
      (HerbrandHMinusOne (L ≃ₐ[K] L)
        (RelativeIdeleGroup.principalSubgroup K L) σ) :=
    hPrincipalDefined.2
  obtain ⟨hC, hmul⟩ :=
    ideleClassHerbrandQuotientDefined_of_principal_relative
      K L σ hgen
  have hcard :
      (Fintype.card (L ≃ₐ[K] L) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hfactor :
      q / (Fintype.card (L ≃ₐ[K] L) : ℚ) ≠ 0 :=
    div_ne_zero hq hcard
  refine ⟨hC, ?_⟩
  apply mul_left_cancel₀ hfactor
  calc
    (q / (Fintype.card (L ≃ₐ[K] L) : ℚ)) *
          @herbrandQuotient
            (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L)
            _ _ _ _ σ hC.1 hC.2 =
        q := by
      rw [← hPrincipal, ← hmul, hRelative]
    _ =
        (q / (Fintype.card (L ≃ₐ[K] L) : ℚ)) *
          (Fintype.card (L ≃ₐ[K] L) : ℚ) := by
      rw [div_mul_cancel₀ q hcard]

omit [NumberField L] in
/-- Norm-index endpoint in group-order form. -/
theorem card_le_ideleClassNorm_index_of_relative_principal_values
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ)
    (hRelativeDefined :
      RelativeIdeleHerbrandQuotientDefined K L σ)
    (hPrincipalDefined :
      PrincipalIdeleHerbrandQuotientDefined K L σ)
    (q : ℚ) (hq : q ≠ 0)
    (hRelative :
      letI := relativeIdeleMulDistribMulAction K L
      letI : Finite
          (HerbrandH0 (L ≃ₐ[K] L)
            (RelativeIdeleGroup K L)) :=
        hRelativeDefined.1
      letI : Finite
          (HerbrandHMinusOne (L ≃ₐ[K] L)
            (RelativeIdeleGroup K L) σ) :=
        hRelativeDefined.2
      herbrandQuotient
          (G := L ≃ₐ[K] L)
          (A := RelativeIdeleGroup K L) σ = q)
    (hPrincipal :
      letI := relativeIdeleMulDistribMulAction K L
      letI := principalIdeleMulDistribMulAction K L
      letI : Finite
          (HerbrandH0 (L ≃ₐ[K] L)
            (RelativeIdeleGroup.principalSubgroup K L)) :=
        hPrincipalDefined.1
      letI : Finite
          (HerbrandHMinusOne (L ≃ₐ[K] L)
            (RelativeIdeleGroup.principalSubgroup K L) σ) :=
        hPrincipalDefined.2
      herbrandQuotient
          (G := L ≃ₐ[K] L)
          (A := RelativeIdeleGroup.principalSubgroup K L) σ =
        q / (Fintype.card (L ≃ₐ[K] L) : ℚ)) :
    Fintype.card (L ≃ₐ[K] L) ≤
      (RelativeIdeleGroup.Cohomology.ideleClassNorm K L).range.index := by
  let := relativeIdeleMulDistribMulAction K L
  let := principalIdeleMulDistribMulAction K L
  let := ideleClassMulDistribMulAction K L
  obtain ⟨hC, hCvalue⟩ :=
    ideleClass_herbrandQuotient_eq_card_of_relative_principal_values
      K L σ hgen hRelativeDefined hPrincipalDefined
        q hq hRelative hPrincipal
  let : Finite
      (HerbrandH0 (L ≃ₐ[K] L)
        (RelativeIdeleGroup.ClassGroup K L)) :=
    hC.1
  let : Finite
      (HerbrandHMinusOne (L ≃ₐ[K] L)
        (RelativeIdeleGroup.ClassGroup K L) σ) :=
    hC.2
  rw [ideleClassNorm_index_eq_herbrandH0_card K L]
  apply
    le_herbrandH0_card_of_herbrandQuotient_eq_nat
      (G := L ≃ₐ[K] L)
      (A := RelativeIdeleGroup.ClassGroup K L)
      σ (Fintype.card (L ≃ₐ[K] L))
  simpa using hCvalue

omit [NumberField L] in
/-- Norm-index endpoint in extension-degree form. -/
theorem finrank_le_ideleClassNorm_index_of_relative_principal_values
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ)
    (hRelativeDefined :
      RelativeIdeleHerbrandQuotientDefined K L σ)
    (hPrincipalDefined :
      PrincipalIdeleHerbrandQuotientDefined K L σ)
    (q : ℚ) (hq : q ≠ 0)
    (hRelative :
      letI := relativeIdeleMulDistribMulAction K L
      letI : Finite
          (HerbrandH0 (L ≃ₐ[K] L)
            (RelativeIdeleGroup K L)) :=
        hRelativeDefined.1
      letI : Finite
          (HerbrandHMinusOne (L ≃ₐ[K] L)
            (RelativeIdeleGroup K L) σ) :=
        hRelativeDefined.2
      herbrandQuotient
          (G := L ≃ₐ[K] L)
          (A := RelativeIdeleGroup K L) σ = q)
    (hPrincipal :
      letI := relativeIdeleMulDistribMulAction K L
      letI := principalIdeleMulDistribMulAction K L
      letI : Finite
          (HerbrandH0 (L ≃ₐ[K] L)
            (RelativeIdeleGroup.principalSubgroup K L)) :=
        hPrincipalDefined.1
      letI : Finite
          (HerbrandHMinusOne (L ≃ₐ[K] L)
            (RelativeIdeleGroup.principalSubgroup K L) σ) :=
        hPrincipalDefined.2
      herbrandQuotient
          (G := L ≃ₐ[K] L)
          (A := RelativeIdeleGroup.principalSubgroup K L) σ =
        q / (Fintype.card (L ≃ₐ[K] L) : ℚ)) :
    Module.finrank K L ≤
      (RelativeIdeleGroup.Cohomology.ideleClassNorm K L).range.index := by
  simpa only [Fintype.card_eq_nat_card,
    IsGalois.card_aut_eq_finrank K L] using
    card_le_ideleClassNorm_index_of_relative_principal_values
      K L σ hgen hRelativeDefined hPrincipalDefined
        q hq hRelative hPrincipal
