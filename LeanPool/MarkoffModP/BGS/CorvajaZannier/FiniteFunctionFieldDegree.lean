/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.FieldTheory.Relrank

/-!
# Frobenius degree of a finite function field

Let `k` be a finite field and put `q = #k`.  The `q`-power Frobenius is a
`k`-algebra endomorphism, since it fixes every element of `k`.  This file
proves that a finite extension `L / k(X)` has degree exactly `q` over the
image of that endomorphism.

This `q` is the cardinality of the constant field, not merely its
characteristic `p`.  Thus `q = p` only when `k` is the prime field.  The
Corvaja--Zannier formulation with `k` contained in a larger field of
cardinality `q ^ m` corresponds to an iterate of this Frobenius step; the
declarations below prove the single `#k`-power step.

No separability hypothesis is required.  Frobenius transports the finite
extension `L / k(X)` to the corresponding extension of image fields, while
the rational function field contributes the factor `q`.
-/

namespace BGS.CorvajaZannier

noncomputable section

open IntermediateField RatFunc
open scoped Polynomial

variable (k : Type*) [Field k] [Fintype k]

/-- In `k(X)`, the image of the `#k`-power Frobenius is exactly
`k(X ^ #k)`. -/
theorem ratFunc_frobeniusFieldRange_eq_adjoin_pow_card :
    (FiniteField.frobeniusAlgHom k k⟮X⟯).fieldRange =
      k⟮(X : k⟮X⟯) ^ Fintype.card k⟯ := by
  calc
    (FiniteField.frobeniusAlgHom k k⟮X⟯).fieldRange =
        (⊤ : IntermediateField k k⟮X⟯).map
          (FiniteField.frobeniusAlgHom k k⟮X⟯) :=
      AlgHom.fieldRange_eq_map _
    _ = k⟮(FiniteField.frobeniusAlgHom k k⟮X⟯) (X : k⟮X⟯)⟯ := by
      rw [← RatFunc.adjoin_X (K := k), IntermediateField.adjoin_map]
      simp
    _ = k⟮(X : k⟮X⟯) ^ Fintype.card k⟯ := by
      rw [FiniteField.frobeniusAlgHom_apply]

/-- The rational function field has degree `#k` over the image of its
`#k`-power Frobenius. -/
theorem ratFunc_finrank_frobeniusFieldRange_eq_card :
    Module.finrank (FiniteField.frobeniusAlgHom k k⟮X⟯).fieldRange k⟮X⟯ =
      Fintype.card k := by
  rw [ratFunc_frobeniusFieldRange_eq_adjoin_pow_card]
  rw [RatFunc.finrank_eq_max_natDegree]
  have hpow : (X : k⟮X⟯) ^ Fintype.card k =
      algebraMap k[X] k⟮X⟯ (Polynomial.X ^ Fintype.card k) := by
    simp
  rw [hpow, RatFunc.num_algebraMap, RatFunc.denom_algebraMap]
  simp

variable {L : Type*} [Field L] [Algebra k L] [Algebra k⟮X⟯ L]
  [IsScalarTower k k⟮X⟯ L] [FiniteDimensional k⟮X⟯ L]

/-- A finite extension of `k(X)` has degree `#k` over the image of its
`#k`-power Frobenius.

The proof compares the two towers through the Frobenius image.  The embedded
rational base contributes degree `#k`, and Frobenius preserves the relative
degree of the finite top extension. -/
theorem finiteFunctionField_finrank_frobeniusFieldRange_eq_card :
    Module.finrank (FiniteField.frobeniusAlgHom k L).fieldRange L =
      Fintype.card k := by
  let i : k⟮X⟯ →ₐ[k] L := Algebra.algHom k k⟮X⟯ L
  let φF : k⟮X⟯ →ₐ[k] k⟮X⟯ := FiniteField.frobeniusAlgHom k k⟮X⟯
  let φL : L →ₐ[k] L := FiniteField.frobeniusAlgHom k L
  let F0 : IntermediateField k L := i.fieldRange
  let Fq0 : IntermediateField k L := φF.fieldRange.map i
  let Lq : IntermediateField k L := φL.fieldRange

  have hcomp : φL.comp i = i.comp φF := by
    ext x
    change (i x) ^ Fintype.card k = i (x ^ Fintype.card k)
    exact (map_pow i x (Fintype.card k)).symm

  have hFmap : F0.map φL = Fq0 := by
    change i.fieldRange.map φL = φF.fieldRange.map i
    rw [AlgHom.map_fieldRange, AlgHom.map_fieldRange, hcomp]

  have hTopMap : (⊤ : IntermediateField k L).map φL = Lq := by
    exact (AlgHom.fieldRange_eq_map φL).symm

  have hRelativeFrobenius :
      IntermediateField.relfinrank Fq0 Lq =
        IntermediateField.relfinrank F0 (⊤ : IntermediateField k L) := by
    have h := IntermediateField.relfinrank_map_map
      F0 (⊤ : IntermediateField k L) φL
    rwa [hFmap, hTopMap] at h

  have hFq0F0 : Fq0 ≤ F0 := by
    change φF.fieldRange.map i ≤ i.fieldRange
    calc
      φF.fieldRange.map i ≤
          (⊤ : IntermediateField k k⟮X⟯).map i :=
        IntermediateField.map_mono i le_top
      _ = i.fieldRange := (AlgHom.fieldRange_eq_map i).symm

  have hFq0Lq : Fq0 ≤ Lq := by
    rw [← hFmap, ← hTopMap]
    exact IntermediateField.map_mono φL le_top

  have hBaseDegree :
      IntermediateField.relfinrank Fq0 F0 = Fintype.card k := by
    have h := IntermediateField.relfinrank_map_map
      φF.fieldRange (⊤ : IntermediateField k k⟮X⟯) i
    change IntermediateField.relfinrank Fq0 F0 = Fintype.card k
    calc
      IntermediateField.relfinrank Fq0 F0 =
          IntermediateField.relfinrank φF.fieldRange
            (⊤ : IntermediateField k k⟮X⟯) := by
        simpa only [Fq0, F0, AlgHom.fieldRange_eq_map] using h
      _ = Module.finrank φF.fieldRange k⟮X⟯ :=
        IntermediateField.relfinrank_top_right _
      _ = Fintype.card k := ratFunc_finrank_frobeniusFieldRange_eq_card k

  have hBaseTower := IntermediateField.relfinrank_mul_relfinrank
    hFq0F0 (show F0 ≤ (⊤ : IntermediateField k L) from le_top)
  have hFrobeniusTower := IntermediateField.relfinrank_mul_relfinrank
    hFq0Lq (show Lq ≤ (⊤ : IntermediateField k L) from le_top)
  rw [hBaseDegree] at hBaseTower
  rw [hRelativeFrobenius] at hFrobeniusTower

  let e : k⟮X⟯ ≃ₐ[k] F0 := i.equivFieldRange
  let b := Module.finBasis k⟮X⟯ L
  let b0 := b.mapCoeffs e.toRingEquiv (by
    intro c x
    simp only [Algebra.smul_def]
    apply congrArg (· * x)
    simp only [e, F0]
    exact Algebra.algHom_apply k k⟮X⟯ L c)
  let : FiniteDimensional F0 L := b0.finiteDimensional_of_finite
  have hF0TopPos : 0 < IntermediateField.relfinrank F0
      (⊤ : IntermediateField k L) := by
    rw [IntermediateField.relfinrank_top_right]
    exact Module.finrank_pos

  have hcancel :
      IntermediateField.relfinrank F0 (⊤ : IntermediateField k L) * Fintype.card k =
        IntermediateField.relfinrank F0 (⊤ : IntermediateField k L) *
          IntermediateField.relfinrank Lq (⊤ : IntermediateField k L) := by
    calc
      _ = Fintype.card k *
          IntermediateField.relfinrank F0 (⊤ : IntermediateField k L) := Nat.mul_comm _ _
      _ = IntermediateField.relfinrank Fq0 (⊤ : IntermediateField k L) := hBaseTower
      _ = IntermediateField.relfinrank F0 (⊤ : IntermediateField k L) *
          IntermediateField.relfinrank Lq (⊤ : IntermediateField k L) :=
        hFrobeniusTower.symm
  have hResult : IntermediateField.relfinrank Lq
      (⊤ : IntermediateField k L) = Fintype.card k := by
    exact (Nat.mul_left_cancel hF0TopPos hcancel).symm
  rw [← IntermediateField.relfinrank_top_right Lq]
  exact hResult

end

end BGS.CorvajaZannier
